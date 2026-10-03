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

/-! Certificates from `NAR4C077C001Part001`. -/


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
noncomputable def nb077_alpha_dummy_000 (F : Class) (I : Class) : Var :=
  (freshVar ((F).fv ∪ (I).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_001 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod
          (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_002 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪
      ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_003 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa
          (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
          (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))
            (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_004 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa
          (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
          (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))
            (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_005 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
          (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
          (syn_wss (syn_cima
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))
            (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_006 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
          (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
          (syn_wss (syn_cima
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))
            (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_007 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
          (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
      ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_008 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (syn_csn (syn_cop (syn_c0c) I))
          (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
      ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_009 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_010 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar
    (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_011 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I)))
          (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod
              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_012 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (syn_cima
            (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I)))
          (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima
            (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I)))
          (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_013 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
          (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
      ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_014 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
          (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
      ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_015 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
      ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_016 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
      ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_017 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
      ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_018 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
      ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_019 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_015 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_020 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_015 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_021 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_022 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_023 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_024 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I)
            (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_017 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_025 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_019 F I)
          (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_019 F I)
          (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_026 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_021 x F I)
          (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_021 x F I)
          (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_027 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_020 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_028 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_020 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_029 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_030 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_031 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_027 F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_027 F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_027 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_032 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_029 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_033 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_034 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_035 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_036 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_037 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_038 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_039 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
          (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I))
          (Class.cv (nb077_alpha_dummy_035 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_040 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
          (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I))
          (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_041 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_035 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_042 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_043 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_044 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_045 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_034 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_046 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_037 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_047 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_035 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_035 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_048 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_038 x F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_049 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_019 F I)
          (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I)
          (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_050 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_021 x F I)
          (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I)
          (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_051 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_052 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_053 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_054 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_055 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
          (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin
          (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
          (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_056 (x : Var) (F : Class) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st))
            (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
          (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin
          (syn_ccom (syn_ccnv (syn_c1st))
            (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
          (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_057 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
            (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))).fv ∪
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_058 (x : Var) (F : Class) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (syn_c1st))
          (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))).fv ∪
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_059 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
          (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_060 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
          (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_061 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
          (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_062 (x : Var) : Var :=
  (freshVar (((syn_ccnv (syn_c1st))).fv ∪
      ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_063 (x : Var) : Var :=
  (freshVar (((syn_ccnv (syn_c1st))).fv ∪
      ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_064 (x : Var) : Var :=
  (freshVar (((syn_ccnv (syn_c1st))).fv ∪
      ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_065 (F : Class) (I : Class) : Var :=
  (freshVar (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪
        ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I)
          (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))
              (Class.cv (nb077_alpha_dummy_061 F I)))
            (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st))
              (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_066 (x : Var) : Var :=
  (freshVar (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪
        ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa
            (syn_wbr (Class.cv (nb077_alpha_dummy_062 x))
              (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))
              (Class.cv (nb077_alpha_dummy_064 x)))
            (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st))
              (Class.cv (nb077_alpha_dummy_063 x)))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_067 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_068 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_069 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_063 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_070 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_063 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_071 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_072 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_073 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_067 F I)
          (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_067 F I)
          (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_074 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_069 x)
          (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_069 x)
          (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_075 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_068 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_076 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_068 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_077 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_070 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_078 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_070 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_079 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_075 F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_075 F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_075 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_080 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_077 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_077 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_077 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_081 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_082 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_083 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_084 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_085 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_086 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_087 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
          (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I))
          (Class.cv (nb077_alpha_dummy_083 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_088 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x))
          (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_089 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_083 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_090 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_086 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_091 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_092 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_093 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_082 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_094 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_085 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_095 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_083 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_083 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_096 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_086 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_086 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_097 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_067 F I)
          (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I)
          (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_098 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_069 x)
          (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x)
          (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_099 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_100 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_101 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_102 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_103 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_061 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_104 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_061 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_105 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_064 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_106 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_064 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_107 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_108 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_109 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_103 F I)
          (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_103 F I)
          (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_110 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_105 x)
          (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_105 x)
          (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_111 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_104 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_112 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_104 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_113 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_106 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_114 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_106 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_115 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_111 F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_111 F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_111 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_116 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_113 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_113 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_113 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_117 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_118 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_119 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_120 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_121 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_122 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_123 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
          (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I))
          (Class.cv (nb077_alpha_dummy_119 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_124 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x))
          (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_125 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_119 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_126 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_122 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_127 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_128 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_129 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_118 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_130 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_121 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_131 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_119 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_119 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_132 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_122 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_122 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_133 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_103 F I)
          (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I)
          (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_134 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_105 x)
          (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x)
          (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_135 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_136 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_137 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_138 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_139 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
          (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_140 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
          (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_141 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
          (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_142 (x : Var) : Var :=
  (freshVar (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_143 (x : Var) : Var :=
  (freshVar (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_144 (x : Var) : Var :=
  (freshVar (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_145 (F : Class) (I : Class) : Var :=
  (freshVar (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪
        ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I)
          (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st)
              (Class.cv (nb077_alpha_dummy_141 F I)))
            (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I))
              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
              (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_146 (x : Var) : Var :=
  (freshVar (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪
        ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa
            (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st)
              (Class.cv (nb077_alpha_dummy_144 x)))
            (syn_wbr (Class.cv (nb077_alpha_dummy_144 x))
              (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
              (Class.cv (nb077_alpha_dummy_143 x)))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_147 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_148 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_149 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_143 x))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part002`. -/


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
noncomputable def nb077_alpha_dummy_150 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_143 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_151 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_152 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_153 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_147 F I)
          (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_147 F I)
          (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_154 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_149 x)
          (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_149 x)
          (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_155 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_148 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_156 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_148 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_157 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_150 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_158 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_150 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_159 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_155 F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_155 F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_155 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_160 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_157 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_157 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_157 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_161 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_162 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_163 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_164 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_165 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_166 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_167 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
          (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I))
          (Class.cv (nb077_alpha_dummy_163 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_168 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x))
          (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_169 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_163 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_170 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_166 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_171 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_172 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_173 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_162 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_174 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_165 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_175 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_163 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_163 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_176 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_166 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_166 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_177 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_147 F I)
          (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I)
          (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_178 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_149 x)
          (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x)
          (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_179 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_180 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_181 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_182 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_183 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_141 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_184 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_141 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_185 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_144 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_186 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_144 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_187 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_188 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_189 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_183 F I)
          (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_183 F I)
          (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_190 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_185 x)
          (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_185 x)
          (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_191 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_184 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_192 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_184 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_193 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_186 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_194 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_186 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_195 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_191 F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_191 F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_191 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_196 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_193 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_193 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_193 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_197 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_198 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_199 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_200 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_201 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_202 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_203 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
          (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I))
          (Class.cv (nb077_alpha_dummy_199 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_204 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x))
          (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_205 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_199 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_206 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_202 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_207 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_208 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_209 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_198 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_210 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_201 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_211 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_199 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_199 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_212 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_202 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_202 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_213 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_183 F I)
          (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I)
          (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_214 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_185 x)
          (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x)
          (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_215 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_216 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_217 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_218 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_219 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_220 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_221 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_143 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_222 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_143 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_223 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_224 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_225 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_219 F I)
          (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_219 F I)
          (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_226 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_221 x)
          (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_221 x)
          (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_227 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_220 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_228 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_220 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_229 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_222 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_230 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_222 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_231 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_227 F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_227 F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_227 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_232 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_229 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_229 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_229 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_233 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_234 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_235 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_236 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_237 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_238 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_239 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
          (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I))
          (Class.cv (nb077_alpha_dummy_235 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_240 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x))
          (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_241 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_235 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_242 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_238 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_243 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_244 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_245 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_234 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_246 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_237 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_247 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_235 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_235 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_248 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_238 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_238 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_249 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_219 F I)
          (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I)
          (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_250 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_221 x)
          (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x)
          (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_251 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_252 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_253 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_254 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_255 (F : Class) (I : Class) : Var :=
  (freshVar (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ((syn_cvv)).fv ∪
      ((syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_256 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_257 (F : Class) (I : Class) : Var :=
  (freshVar (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪
        ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv))
          (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I))
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_258 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
          (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x))
            (syn_cplc (Class.cv x) (syn_c1c))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_259 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_255 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_260 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_255 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_261 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_262 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_263 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_264 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x)
            (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_261 x)
            (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_265 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_259 F I)
          (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_259 F I)
          (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_266 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_261 x)
          (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_267 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_260 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_268 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_260 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_269 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_262 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_270 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_262 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_271 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_267 F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_267 F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_267 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_272 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_269 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_269 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_269 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_273 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_274 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_275 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_276 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_277 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_278 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_279 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
          (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I))
          (Class.cv (nb077_alpha_dummy_275 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_280 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x))
          (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_281 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_275 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_282 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_278 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_283 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_284 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_285 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_274 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_286 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_277 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_287 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_275 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_275 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_288 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_278 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_278 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_289 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_259 F I)
          (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I)
          (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_290 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_261 x)
          (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x)
          (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_291 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_292 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_293 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_294 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_295 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_296 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_297 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_298 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_299 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part003`. -/


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
noncomputable def nb077_alpha_dummy_300 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_301 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
          (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I))
          (Class.cv (nb077_alpha_dummy_297 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_302 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x))
          (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_303 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_297 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_304 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_300 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_305 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_306 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_307 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_296 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_308 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_299 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_309 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_297 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_297 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_310 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_300 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_300 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_311 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_312 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_313 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_063 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_314 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_063 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_315 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_316 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_317 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_311 F I)
          (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_311 F I)
          (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
              (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_318 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_313 x)
          (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv ∪
      ((Class.cab (nb077_alpha_dummy_313 x)
          (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
              (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_319 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_312 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_320 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_312 F I))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_321 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_314 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_322 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_314 x))).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_323 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_319 F I)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_319 F I)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_319 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_324 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_321 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb077_alpha_dummy_321 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb077_alpha_dummy_321 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_325 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_326 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_327 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_328 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_329 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb077_alpha_dummy_330 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb077_alpha_dummy_331 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I))
          (Class.cv (nb077_alpha_dummy_327 F I)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I))
          (Class.cv (nb077_alpha_dummy_327 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_332 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_329 x))
          (Class.cv (nb077_alpha_dummy_330 x)))).fv ∪
      ((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv)
    0)

@[expose]
noncomputable def nb077_alpha_dummy_333 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_327 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_334 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_330 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_335 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_326 F I)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_327 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_336 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_329 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb077_alpha_dummy_330 x)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_337 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_326 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_338 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_329 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_339 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_327 F I))).fv ∪
      ((Class.cv (nb077_alpha_dummy_327 F I))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_340 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077_alpha_dummy_330 x))).fv ∪
      ((Class.cv (nb077_alpha_dummy_330 x))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_341 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_311 F I)
          (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I)
          (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_342 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077_alpha_dummy_313 x)
          (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x)
          (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
            (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
              (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_343 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_344 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_345 (F : Class) (I : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv) 0)

@[expose]
noncomputable def nb077_alpha_dummy_346 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv ∪
      ((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv) 0)

theorem nb077_fresh_000 (F : Class) (I : Class) :
    (nb077_alpha_dummy_003 F I) ∉
      (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I))
              (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_001 F I)))
              (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_003] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I))
              (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_001 F I)))
              (Class.cv (nb077_alpha_dummy_001 F I)))))).fv)
      0

theorem nb077_fresh_001 (F : Class) (I : Class) :
    (nb077_alpha_dummy_004 F I) ∉
      (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I))
              (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_001 F I)))
              (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_004] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I))
              (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_001 F I)))
              (Class.cv (nb077_alpha_dummy_001 F I)))))).fv)
      1

theorem nb077_distinct_002 (F : Class) (I : Class) :
    (nb077_alpha_dummy_003 F I) ≠ (nb077_alpha_dummy_004 F I) := by
  simpa only [nb077_alpha_dummy_003, nb077_alpha_dummy_004] using
    (freshVar_injective (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa
            (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
            (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_001 F I)))
              (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_003 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_005 x F I) ∉
      (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
            (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
            (syn_wss (syn_cima
                (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_002 x F I)))
              (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
            (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
            (syn_wss (syn_cima
                (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_002 x F I)))
              (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv)
      0

theorem nb077_fresh_004 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_006 x F I) ∉
      (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
            (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
            (syn_wss (syn_cima
                (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_002 x F I)))
              (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
            (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
            (syn_wss (syn_cima
                (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_002 x F I)))
              (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv)
      1

theorem nb077_distinct_005 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_005 x F I) ≠ (nb077_alpha_dummy_006 x F I) := by
  simpa only [nb077_alpha_dummy_005, nb077_alpha_dummy_006] using
    (freshVar_injective (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
            (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
            (syn_wss (syn_cima
                (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_002 x F I)))
              (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_006 (F : Class) (I : Class) :
    (nb077_alpha_dummy_049 F I) ∉
      (((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_007 (F : Class) (I : Class) :
    (nb077_alpha_dummy_025 F I) ∉
      (((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_025] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv)
      0

theorem nb077_fresh_008 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_050 x F I) ∉
      (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_017 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I)
            (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_017 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I)
            (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_009 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_026 x F I) ∉
      (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_026] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv)
      0

theorem nb077_fresh_010 (F : Class) (I : Class) :
    (nb077_alpha_dummy_073 F I) ∉
      (((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv)
      0

theorem nb077_fresh_011 (F : Class) (I : Class) :
    (nb077_alpha_dummy_097 F I) ∉
      (((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_097] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_012 (x : Var) :
    (nb077_alpha_dummy_074 x) ∉
      (((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv)
      0

theorem nb077_fresh_013 (x : Var) :
    (nb077_alpha_dummy_098 x) ∉
      (((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_098] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_014 (F : Class) (I : Class) :
    (nb077_alpha_dummy_109 F I) ∉
      (((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_109] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv)
      0

theorem nb077_fresh_015 (F : Class) (I : Class) :
    (nb077_alpha_dummy_133 F I) ∉
      (((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_133] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_016 (x : Var) :
    (nb077_alpha_dummy_110 x) ∉
      (((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_110] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv)
      0

theorem nb077_fresh_017 (x : Var) :
    (nb077_alpha_dummy_134 x) ∉
      (((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_134] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_018 (F : Class) (I : Class) :
    (nb077_alpha_dummy_153 F I) ∉
      (((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_153] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv)
      0

theorem nb077_fresh_019 (F : Class) (I : Class) :
    (nb077_alpha_dummy_177 F I) ∉
      (((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_177] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_020 (x : Var) :
    (nb077_alpha_dummy_154 x) ∉
      (((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv)
      0

theorem nb077_fresh_021 (x : Var) :
    (nb077_alpha_dummy_178 x) ∉
      (((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_178] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_022 (F : Class) (I : Class) :
    (nb077_alpha_dummy_189 F I) ∉
      (((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_189] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv)
      0

theorem nb077_fresh_023 (F : Class) (I : Class) :
    (nb077_alpha_dummy_213 F I) ∉
      (((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_213] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_024 (x : Var) :
    (nb077_alpha_dummy_190 x) ∉
      (((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_190] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv)
      0

theorem nb077_fresh_025 (x : Var) :
    (nb077_alpha_dummy_214 x) ∉
      (((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_214] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_026 (F : Class) (I : Class) :
    (nb077_alpha_dummy_249 F I) ∉
      (((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_249] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_027 (F : Class) (I : Class) :
    (nb077_alpha_dummy_225 F I) ∉
      (((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_225] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv)
      0

theorem nb077_fresh_028 (x : Var) :
    (nb077_alpha_dummy_250 x) ∉
      (((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_250] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_029 (x : Var) :
    (nb077_alpha_dummy_226 x) ∉
      (((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_226] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv)
      0

theorem nb077_fresh_030 (F : Class) (I : Class) :
    (nb077_alpha_dummy_265 F I) ∉
      (((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_265] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv)
      0

theorem nb077_fresh_031 (F : Class) (I : Class) :
    (nb077_alpha_dummy_289 F I) ∉
      (((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_289] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_032 (x : Var) :
    (nb077_alpha_dummy_290 x) ∉
      (((Class.cab (nb077_alpha_dummy_261 x)
            (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x)
            (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_290] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_261 x)
            (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x)
            (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_033 (x : Var) :
    (nb077_alpha_dummy_266 x) ∉
      (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_266] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv)
      0

theorem nb077_fresh_034 (F : Class) (I : Class) :
    (nb077_alpha_dummy_341 F I) ∉
      (((Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_341] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_035 (F : Class) (I : Class) :
    (nb077_alpha_dummy_317 F I) ∉
      (((Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_317] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv)
      0

theorem nb077_fresh_036 (x : Var) :
    (nb077_alpha_dummy_342 x) ∉
      (((Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_342] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb077_fresh_037 (x : Var) :
    (nb077_alpha_dummy_318 x) ∉
      (((Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_318] using
    freshVar_not_mem
      (((Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv ∪
        ((Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv)
      0

theorem nb077_fresh_038 (F : Class) (I : Class) :
    (nb077_alpha_dummy_259 F I) ∉
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_255 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_259] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_255 F I))).fv)
      0

theorem nb077_fresh_039 (F : Class) (I : Class) :
    (nb077_alpha_dummy_260 F I) ∉
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_255 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_260] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_255 F I))).fv)
      1

theorem nb077_distinct_040 (F : Class) (I : Class) :
    (nb077_alpha_dummy_259 F I) ≠ (nb077_alpha_dummy_260 F I) := by
  simpa only [nb077_alpha_dummy_259, nb077_alpha_dummy_260] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_255 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_041 (F : Class) (I : Class) :
    (nb077_alpha_dummy_295 F I) ∉
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_295] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_042 (F : Class) (I : Class) :
    (nb077_alpha_dummy_296 F I) ∉
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_296] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_043 (F : Class) (I : Class) :
    (nb077_alpha_dummy_297 F I) ∉
      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_297] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_044 (F : Class) (I : Class) :
    (nb077_alpha_dummy_295 F I) ≠ (nb077_alpha_dummy_296 F I) := by
  simpa only [nb077_alpha_dummy_295, nb077_alpha_dummy_296] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_045 (F : Class) (I : Class) :
    (nb077_alpha_dummy_295 F I) ≠ (nb077_alpha_dummy_297 F I) := by
  simpa only [nb077_alpha_dummy_295, nb077_alpha_dummy_297] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_046 (F : Class) (I : Class) :
    (nb077_alpha_dummy_296 F I) ≠ (nb077_alpha_dummy_297 F I) := by
  simpa only [nb077_alpha_dummy_296, nb077_alpha_dummy_297] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_047 (F : Class) (I : Class) :
    (nb077_alpha_dummy_019 F I) ∉
      (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_019] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv)
      0

theorem nb077_fresh_048 (F : Class) (I : Class) :
    (nb077_alpha_dummy_020 F I) ∉
      (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_020] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv)
      1

theorem nb077_distinct_049 (F : Class) (I : Class) :
    (nb077_alpha_dummy_019 F I) ≠ (nb077_alpha_dummy_020 F I) := by
  simpa only [nb077_alpha_dummy_019, nb077_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_050 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_021 x F I) ∉
      (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_021] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_017 x F I))).fv)
      0

theorem nb077_fresh_051 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_022 x F I) ∉
      (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_022] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_017 x F I))).fv)
      1

theorem nb077_distinct_052 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_021 x F I) ≠ (nb077_alpha_dummy_022 x F I) := by
  simpa only [nb077_alpha_dummy_021, nb077_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_053 (F : Class) (I : Class) :
    (nb077_alpha_dummy_027 F I) ∉ (((Class.cv (nb077_alpha_dummy_020 F I))).fv) := by
  simpa only [nb077_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_020 F I))).fv) 0

theorem nb077_fresh_054 (F : Class) (I : Class) :
    (nb077_alpha_dummy_028 F I) ∉ (((Class.cv (nb077_alpha_dummy_020 F I))).fv) := by
  simpa only [nb077_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_020 F I))).fv) 1

theorem nb077_distinct_055 (F : Class) (I : Class) :
    (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_028 F I) := by
  simpa only [nb077_alpha_dummy_027, nb077_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_056 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_029 x F I) ∉ (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_029] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) 0

theorem nb077_fresh_057 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_030 x F I) ∉ (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_030] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) 1

theorem nb077_distinct_058 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_030 x F I) := by
  simpa only [nb077_alpha_dummy_029, nb077_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_059 (F : Class) (I : Class) :
    (nb077_alpha_dummy_033 F I) ∉
      (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_060 (F : Class) (I : Class) :
    (nb077_alpha_dummy_034 F I) ∉
      (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_034] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_061 (F : Class) (I : Class) :
    (nb077_alpha_dummy_035 F I) ∉
      (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_035] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_062 (F : Class) (I : Class) :
    (nb077_alpha_dummy_033 F I) ≠ (nb077_alpha_dummy_034 F I) := by
  simpa only [nb077_alpha_dummy_033, nb077_alpha_dummy_034] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_063 (F : Class) (I : Class) :
    (nb077_alpha_dummy_033 F I) ≠ (nb077_alpha_dummy_035 F I) := by
  simpa only [nb077_alpha_dummy_033, nb077_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_064 (F : Class) (I : Class) :
    (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_035 F I) := by
  simpa only [nb077_alpha_dummy_034, nb077_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_065 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_036 x F I) ∉
      (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_036] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_066 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_037 x F I) ∉
      (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_037] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_067 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_038 x F I) ∉
      (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_038] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_068 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_036 x F I) ≠ (nb077_alpha_dummy_037 x F I) := by
  simpa only [nb077_alpha_dummy_036, nb077_alpha_dummy_037] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part004`. -/


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

theorem nb077_distinct_069 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_036 x F I) ≠ (nb077_alpha_dummy_038 x F I) := by
  simpa only [nb077_alpha_dummy_036, nb077_alpha_dummy_038] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_070 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_038 x F I) := by
  simpa only [nb077_alpha_dummy_037, nb077_alpha_dummy_038] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_071 (F : Class) (I : Class) :
    (nb077_alpha_dummy_045 F I) ∉
      (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_034 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_034 F I))).fv)
      0

theorem nb077_fresh_072 (F : Class) (I : Class) :
    (nb077_alpha_dummy_041 F I) ∉
      (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_035 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_035 F I))).fv)
      0

theorem nb077_fresh_073 (F : Class) (I : Class) :
    (nb077_alpha_dummy_047 F I) ∉
      (((Class.cv (nb077_alpha_dummy_035 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_035 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_035 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_035 F I))).fv)
      0

theorem nb077_fresh_074 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_046 x F I) ∉
      (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_037 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_037 x F I))).fv)
      0

theorem nb077_fresh_075 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_042 x F I) ∉
      (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_038 x F I))).fv)
      0

theorem nb077_fresh_076 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_048 x F I) ∉
      (((Class.cv (nb077_alpha_dummy_038 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_038 x F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_038 x F I))).fv)
      0

theorem nb077_fresh_077 (F : Class) (I : Class) :
    (nb077_alpha_dummy_067 F I) ∉
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_067] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv)
      0

theorem nb077_fresh_078 (F : Class) (I : Class) :
    (nb077_alpha_dummy_068 F I) ∉
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv)
      1

theorem nb077_distinct_079 (F : Class) (I : Class) :
    (nb077_alpha_dummy_067 F I) ≠ (nb077_alpha_dummy_068 F I) := by
  simpa only [nb077_alpha_dummy_067, nb077_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_080 (F : Class) (I : Class) :
    (nb077_alpha_dummy_103 F I) ∉
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_103] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv)
      0

theorem nb077_fresh_081 (F : Class) (I : Class) :
    (nb077_alpha_dummy_104 F I) ∉
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_104] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv)
      1

theorem nb077_distinct_082 (F : Class) (I : Class) :
    (nb077_alpha_dummy_103 F I) ≠ (nb077_alpha_dummy_104 F I) := by
  simpa only [nb077_alpha_dummy_103, nb077_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_083 (F : Class) (I : Class) :
    (nb077_alpha_dummy_311 F I) ∉
      (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_311] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv)
      0

theorem nb077_fresh_084 (F : Class) (I : Class) :
    (nb077_alpha_dummy_312 F I) ∉
      (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_312] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv)
      1

theorem nb077_distinct_085 (F : Class) (I : Class) :
    (nb077_alpha_dummy_311 F I) ≠ (nb077_alpha_dummy_312 F I) := by
  simpa only [nb077_alpha_dummy_311, nb077_alpha_dummy_312] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_086 (x : Var) :
    (nb077_alpha_dummy_069 x) ∉
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
      0

theorem nb077_fresh_087 (x : Var) :
    (nb077_alpha_dummy_070 x) ∉
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
      1

theorem nb077_distinct_088 (x : Var) :
    (nb077_alpha_dummy_069 x) ≠ (nb077_alpha_dummy_070 x) := by
  simpa only [nb077_alpha_dummy_069, nb077_alpha_dummy_070] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_063 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_089 (x : Var) :
    (nb077_alpha_dummy_105 x) ∉
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_105] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv)
      0

theorem nb077_fresh_090 (x : Var) :
    (nb077_alpha_dummy_106 x) ∉
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_106] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv)
      1

theorem nb077_distinct_091 (x : Var) :
    (nb077_alpha_dummy_105 x) ≠ (nb077_alpha_dummy_106 x) := by
  simpa only [nb077_alpha_dummy_105, nb077_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_064 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_092 (x : Var) :
    (nb077_alpha_dummy_313 x) ∉
      (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_313] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
      0

theorem nb077_fresh_093 (x : Var) :
    (nb077_alpha_dummy_314 x) ∉
      (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_314] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
      1

theorem nb077_distinct_094 (x : Var) :
    (nb077_alpha_dummy_313 x) ≠ (nb077_alpha_dummy_314 x) := by
  simpa only [nb077_alpha_dummy_313, nb077_alpha_dummy_314] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_063 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_095 (F : Class) (I : Class) :
    (nb077_alpha_dummy_075 F I) ∉ (((Class.cv (nb077_alpha_dummy_068 F I))).fv) := by
  simpa only [nb077_alpha_dummy_075] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_068 F I))).fv) 0

theorem nb077_fresh_096 (F : Class) (I : Class) :
    (nb077_alpha_dummy_076 F I) ∉ (((Class.cv (nb077_alpha_dummy_068 F I))).fv) := by
  simpa only [nb077_alpha_dummy_076] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_068 F I))).fv) 1

theorem nb077_distinct_097 (F : Class) (I : Class) :
    (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_076 F I) := by
  simpa only [nb077_alpha_dummy_075, nb077_alpha_dummy_076] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_068 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_098 (x : Var) :
    (nb077_alpha_dummy_077 x) ∉ (((Class.cv (nb077_alpha_dummy_070 x))).fv) := by
  simpa only [nb077_alpha_dummy_077] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_070 x))).fv) 0

theorem nb077_fresh_099 (x : Var) :
    (nb077_alpha_dummy_078 x) ∉ (((Class.cv (nb077_alpha_dummy_070 x))).fv) := by
  simpa only [nb077_alpha_dummy_078] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_070 x))).fv) 1

theorem nb077_distinct_100 (x : Var) :
    (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_078 x) := by
  simpa only [nb077_alpha_dummy_077, nb077_alpha_dummy_078] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_070 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_101 (F : Class) (I : Class) :
    (nb077_alpha_dummy_081 F I) ∉
      (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_102 (F : Class) (I : Class) :
    (nb077_alpha_dummy_082 F I) ∉
      (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_082] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_103 (F : Class) (I : Class) :
    (nb077_alpha_dummy_083 F I) ∉
      (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_083] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_104 (F : Class) (I : Class) :
    (nb077_alpha_dummy_081 F I) ≠ (nb077_alpha_dummy_082 F I) := by
  simpa only [nb077_alpha_dummy_081, nb077_alpha_dummy_082] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_105 (F : Class) (I : Class) :
    (nb077_alpha_dummy_081 F I) ≠ (nb077_alpha_dummy_083 F I) := by
  simpa only [nb077_alpha_dummy_081, nb077_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_106 (F : Class) (I : Class) :
    (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_083 F I) := by
  simpa only [nb077_alpha_dummy_082, nb077_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_107 (x : Var) :
    (nb077_alpha_dummy_084 x) ∉
      (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_084] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_108 (x : Var) :
    (nb077_alpha_dummy_085 x) ∉
      (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_085] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_109 (x : Var) :
    (nb077_alpha_dummy_086 x) ∉
      (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_086] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_110 (x : Var) :
    (nb077_alpha_dummy_084 x) ≠ (nb077_alpha_dummy_085 x) := by
  simpa only [nb077_alpha_dummy_084, nb077_alpha_dummy_085] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_111 (x : Var) :
    (nb077_alpha_dummy_084 x) ≠ (nb077_alpha_dummy_086 x) := by
  simpa only [nb077_alpha_dummy_084, nb077_alpha_dummy_086] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_112 (x : Var) :
    (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_086 x) := by
  simpa only [nb077_alpha_dummy_085, nb077_alpha_dummy_086] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_113 (F : Class) (I : Class) :
    (nb077_alpha_dummy_093 F I) ∉
      (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_082 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_082 F I))).fv)
      0

theorem nb077_fresh_114 (F : Class) (I : Class) :
    (nb077_alpha_dummy_089 F I) ∉
      (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_083 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_089] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_083 F I))).fv)
      0

theorem nb077_fresh_115 (F : Class) (I : Class) :
    (nb077_alpha_dummy_095 F I) ∉
      (((Class.cv (nb077_alpha_dummy_083 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_083 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_095] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_083 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_083 F I))).fv)
      0

theorem nb077_fresh_116 (x : Var) :
    (nb077_alpha_dummy_094 x) ∉
      (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_085 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_085 x))).fv)
      0

theorem nb077_fresh_117 (x : Var) :
    (nb077_alpha_dummy_090 x) ∉
      (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_090] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv)
      0

theorem nb077_fresh_118 (x : Var) :
    (nb077_alpha_dummy_096 x) ∉
      (((Class.cv (nb077_alpha_dummy_086 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_096] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_086 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv)
      0

theorem nb077_fresh_119 (F : Class) (I : Class) :
    (nb077_alpha_dummy_111 F I) ∉ (((Class.cv (nb077_alpha_dummy_104 F I))).fv) := by
  simpa only [nb077_alpha_dummy_111] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_104 F I))).fv) 0

theorem nb077_fresh_120 (F : Class) (I : Class) :
    (nb077_alpha_dummy_112 F I) ∉ (((Class.cv (nb077_alpha_dummy_104 F I))).fv) := by
  simpa only [nb077_alpha_dummy_112] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_104 F I))).fv) 1

theorem nb077_distinct_121 (F : Class) (I : Class) :
    (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_112 F I) := by
  simpa only [nb077_alpha_dummy_111, nb077_alpha_dummy_112] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_104 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_122 (x : Var) :
    (nb077_alpha_dummy_113 x) ∉ (((Class.cv (nb077_alpha_dummy_106 x))).fv) := by
  simpa only [nb077_alpha_dummy_113] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_106 x))).fv) 0

theorem nb077_fresh_123 (x : Var) :
    (nb077_alpha_dummy_114 x) ∉ (((Class.cv (nb077_alpha_dummy_106 x))).fv) := by
  simpa only [nb077_alpha_dummy_114] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_106 x))).fv) 1

theorem nb077_distinct_124 (x : Var) :
    (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_114 x) := by
  simpa only [nb077_alpha_dummy_113, nb077_alpha_dummy_114] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_106 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_125 (F : Class) (I : Class) :
    (nb077_alpha_dummy_117 F I) ∉
      (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_117] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_126 (F : Class) (I : Class) :
    (nb077_alpha_dummy_118 F I) ∉
      (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_118] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_127 (F : Class) (I : Class) :
    (nb077_alpha_dummy_119 F I) ∉
      (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_119] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_128 (F : Class) (I : Class) :
    (nb077_alpha_dummy_117 F I) ≠ (nb077_alpha_dummy_118 F I) := by
  simpa only [nb077_alpha_dummy_117, nb077_alpha_dummy_118] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_129 (F : Class) (I : Class) :
    (nb077_alpha_dummy_117 F I) ≠ (nb077_alpha_dummy_119 F I) := by
  simpa only [nb077_alpha_dummy_117, nb077_alpha_dummy_119] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_130 (F : Class) (I : Class) :
    (nb077_alpha_dummy_118 F I) ≠ (nb077_alpha_dummy_119 F I) := by
  simpa only [nb077_alpha_dummy_118, nb077_alpha_dummy_119] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_131 (x : Var) :
    (nb077_alpha_dummy_120 x) ∉
      (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_120] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_132 (x : Var) :
    (nb077_alpha_dummy_121 x) ∉
      (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_121] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_133 (x : Var) :
    (nb077_alpha_dummy_122 x) ∉
      (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_122] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_134 (x : Var) :
    (nb077_alpha_dummy_120 x) ≠ (nb077_alpha_dummy_121 x) := by
  simpa only [nb077_alpha_dummy_120, nb077_alpha_dummy_121] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_135 (x : Var) :
    (nb077_alpha_dummy_120 x) ≠ (nb077_alpha_dummy_122 x) := by
  simpa only [nb077_alpha_dummy_120, nb077_alpha_dummy_122] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_136 (x : Var) :
    (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_122 x) := by
  simpa only [nb077_alpha_dummy_121, nb077_alpha_dummy_122] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_137 (F : Class) (I : Class) :
    (nb077_alpha_dummy_129 F I) ∉
      (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_118 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_129] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_118 F I))).fv)
      0

theorem nb077_fresh_138 (F : Class) (I : Class) :
    (nb077_alpha_dummy_125 F I) ∉
      (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_119 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_125] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_119 F I))).fv)
      0

theorem nb077_fresh_139 (F : Class) (I : Class) :
    (nb077_alpha_dummy_131 F I) ∉
      (((Class.cv (nb077_alpha_dummy_119 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_119 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_131] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_119 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_119 F I))).fv)
      0

theorem nb077_fresh_140 (x : Var) :
    (nb077_alpha_dummy_130 x) ∉
      (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_121 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_130] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_121 x))).fv)
      0

theorem nb077_fresh_141 (x : Var) :
    (nb077_alpha_dummy_126 x) ∉
      (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_126] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv)
      0

theorem nb077_fresh_142 (x : Var) :
    (nb077_alpha_dummy_132 x) ∉
      (((Class.cv (nb077_alpha_dummy_122 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_132] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_122 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv)
      0

theorem nb077_fresh_143 (F : Class) (I : Class) :
    (nb077_alpha_dummy_147 F I) ∉
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_147] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv)
      0

theorem nb077_fresh_144 (F : Class) (I : Class) :
    (nb077_alpha_dummy_148 F I) ∉
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_148] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv)
      1

theorem nb077_distinct_145 (F : Class) (I : Class) :
    (nb077_alpha_dummy_147 F I) ≠ (nb077_alpha_dummy_148 F I) := by
  simpa only [nb077_alpha_dummy_147, nb077_alpha_dummy_148] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_146 (F : Class) (I : Class) :
    (nb077_alpha_dummy_183 F I) ∉
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_141 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_183] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_141 F I))).fv)
      0

theorem nb077_fresh_147 (F : Class) (I : Class) :
    (nb077_alpha_dummy_184 F I) ∉
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_141 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_184] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_141 F I))).fv)
      1

theorem nb077_distinct_148 (F : Class) (I : Class) :
    (nb077_alpha_dummy_183 F I) ≠ (nb077_alpha_dummy_184 F I) := by
  simpa only [nb077_alpha_dummy_183, nb077_alpha_dummy_184] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_141 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_149 (F : Class) (I : Class) :
    (nb077_alpha_dummy_219 F I) ∉
      (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_219] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv)
      0

theorem nb077_fresh_150 (F : Class) (I : Class) :
    (nb077_alpha_dummy_220 F I) ∉
      (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_220] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv)
      1

theorem nb077_distinct_151 (F : Class) (I : Class) :
    (nb077_alpha_dummy_219 F I) ≠ (nb077_alpha_dummy_220 F I) := by
  simpa only [nb077_alpha_dummy_219, nb077_alpha_dummy_220] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_152 (x : Var) :
    (nb077_alpha_dummy_149 x) ∉
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_149] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv)
      0

theorem nb077_fresh_153 (x : Var) :
    (nb077_alpha_dummy_150 x) ∉
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_150] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv)
      1

theorem nb077_distinct_154 (x : Var) :
    (nb077_alpha_dummy_149 x) ≠ (nb077_alpha_dummy_150 x) := by
  simpa only [nb077_alpha_dummy_149, nb077_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_143 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_155 (x : Var) :
    (nb077_alpha_dummy_185 x) ∉
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_185] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv)
      0

theorem nb077_fresh_156 (x : Var) :
    (nb077_alpha_dummy_186 x) ∉
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_186] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv)
      1

theorem nb077_distinct_157 (x : Var) :
    (nb077_alpha_dummy_185 x) ≠ (nb077_alpha_dummy_186 x) := by
  simpa only [nb077_alpha_dummy_185, nb077_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_144 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_158 (x : Var) :
    (nb077_alpha_dummy_221 x) ∉
      (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_221] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv)
      0

theorem nb077_fresh_159 (x : Var) :
    (nb077_alpha_dummy_222 x) ∉
      (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_222] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv)
      1

theorem nb077_distinct_160 (x : Var) :
    (nb077_alpha_dummy_221 x) ≠ (nb077_alpha_dummy_222 x) := by
  simpa only [nb077_alpha_dummy_221, nb077_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_143 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_161 (F : Class) (I : Class) :
    (nb077_alpha_dummy_155 F I) ∉ (((Class.cv (nb077_alpha_dummy_148 F I))).fv) := by
  simpa only [nb077_alpha_dummy_155] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_148 F I))).fv) 0

theorem nb077_fresh_162 (F : Class) (I : Class) :
    (nb077_alpha_dummy_156 F I) ∉ (((Class.cv (nb077_alpha_dummy_148 F I))).fv) := by
  simpa only [nb077_alpha_dummy_156] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_148 F I))).fv) 1

theorem nb077_distinct_163 (F : Class) (I : Class) :
    (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_156 F I) := by
  simpa only [nb077_alpha_dummy_155, nb077_alpha_dummy_156] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_148 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_164 (x : Var) :
    (nb077_alpha_dummy_157 x) ∉ (((Class.cv (nb077_alpha_dummy_150 x))).fv) := by
  simpa only [nb077_alpha_dummy_157] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_150 x))).fv) 0

theorem nb077_fresh_165 (x : Var) :
    (nb077_alpha_dummy_158 x) ∉ (((Class.cv (nb077_alpha_dummy_150 x))).fv) := by
  simpa only [nb077_alpha_dummy_158] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_150 x))).fv) 1

theorem nb077_distinct_166 (x : Var) :
    (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_158 x) := by
  simpa only [nb077_alpha_dummy_157, nb077_alpha_dummy_158] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_150 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_167 (F : Class) (I : Class) :
    (nb077_alpha_dummy_161 F I) ∉
      (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_161] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_168 (F : Class) (I : Class) :
    (nb077_alpha_dummy_162 F I) ∉
      (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_162] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_169 (F : Class) (I : Class) :
    (nb077_alpha_dummy_163 F I) ∉
      (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_163] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_170 (F : Class) (I : Class) :
    (nb077_alpha_dummy_161 F I) ≠ (nb077_alpha_dummy_162 F I) := by
  simpa only [nb077_alpha_dummy_161, nb077_alpha_dummy_162] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_171 (F : Class) (I : Class) :
    (nb077_alpha_dummy_161 F I) ≠ (nb077_alpha_dummy_163 F I) := by
  simpa only [nb077_alpha_dummy_161, nb077_alpha_dummy_163] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_172 (F : Class) (I : Class) :
    (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_163 F I) := by
  simpa only [nb077_alpha_dummy_162, nb077_alpha_dummy_163] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_173 (x : Var) :
    (nb077_alpha_dummy_164 x) ∉
      (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_164] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_174 (x : Var) :
    (nb077_alpha_dummy_165 x) ∉
      (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_165] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_175 (x : Var) :
    (nb077_alpha_dummy_166 x) ∉
      (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_166] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_176 (x : Var) :
    (nb077_alpha_dummy_164 x) ≠ (nb077_alpha_dummy_165 x) := by
  simpa only [nb077_alpha_dummy_164, nb077_alpha_dummy_165] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_177 (x : Var) :
    (nb077_alpha_dummy_164 x) ≠ (nb077_alpha_dummy_166 x) := by
  simpa only [nb077_alpha_dummy_164, nb077_alpha_dummy_166] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_178 (x : Var) :
    (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_166 x) := by
  simpa only [nb077_alpha_dummy_165, nb077_alpha_dummy_166] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_179 (F : Class) (I : Class) :
    (nb077_alpha_dummy_173 F I) ∉
      (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_162 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_173] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_162 F I))).fv)
      0

theorem nb077_fresh_180 (F : Class) (I : Class) :
    (nb077_alpha_dummy_169 F I) ∉
      (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_163 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_169] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_163 F I))).fv)
      0

theorem nb077_fresh_181 (F : Class) (I : Class) :
    (nb077_alpha_dummy_175 F I) ∉
      (((Class.cv (nb077_alpha_dummy_163 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_163 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_175] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_163 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_163 F I))).fv)
      0

theorem nb077_fresh_182 (x : Var) :
    (nb077_alpha_dummy_174 x) ∉
      (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_165 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_174] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_165 x))).fv)
      0

theorem nb077_fresh_183 (x : Var) :
    (nb077_alpha_dummy_170 x) ∉
      (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_170] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv)
      0

theorem nb077_fresh_184 (x : Var) :
    (nb077_alpha_dummy_176 x) ∉
      (((Class.cv (nb077_alpha_dummy_166 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_176] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_166 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv)
      0

theorem nb077_fresh_185 (F : Class) (I : Class) :
    (nb077_alpha_dummy_191 F I) ∉ (((Class.cv (nb077_alpha_dummy_184 F I))).fv) := by
  simpa only [nb077_alpha_dummy_191] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_184 F I))).fv) 0

theorem nb077_fresh_186 (F : Class) (I : Class) :
    (nb077_alpha_dummy_192 F I) ∉ (((Class.cv (nb077_alpha_dummy_184 F I))).fv) := by
  simpa only [nb077_alpha_dummy_192] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_184 F I))).fv) 1

theorem nb077_distinct_187 (F : Class) (I : Class) :
    (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_192 F I) := by
  simpa only [nb077_alpha_dummy_191, nb077_alpha_dummy_192] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_184 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_188 (x : Var) :
    (nb077_alpha_dummy_193 x) ∉ (((Class.cv (nb077_alpha_dummy_186 x))).fv) := by
  simpa only [nb077_alpha_dummy_193] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_186 x))).fv) 0

theorem nb077_fresh_189 (x : Var) :
    (nb077_alpha_dummy_194 x) ∉ (((Class.cv (nb077_alpha_dummy_186 x))).fv) := by
  simpa only [nb077_alpha_dummy_194] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_186 x))).fv) 1

theorem nb077_distinct_190 (x : Var) :
    (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_194 x) := by
  simpa only [nb077_alpha_dummy_193, nb077_alpha_dummy_194] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_186 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_191 (F : Class) (I : Class) :
    (nb077_alpha_dummy_197 F I) ∉
      (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_197] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_192 (F : Class) (I : Class) :
    (nb077_alpha_dummy_198 F I) ∉
      (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_198] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_193 (F : Class) (I : Class) :
    (nb077_alpha_dummy_199 F I) ∉
      (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_199] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_194 (F : Class) (I : Class) :
    (nb077_alpha_dummy_197 F I) ≠ (nb077_alpha_dummy_198 F I) := by
  simpa only [nb077_alpha_dummy_197, nb077_alpha_dummy_198] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_195 (F : Class) (I : Class) :
    (nb077_alpha_dummy_197 F I) ≠ (nb077_alpha_dummy_199 F I) := by
  simpa only [nb077_alpha_dummy_197, nb077_alpha_dummy_199] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_196 (F : Class) (I : Class) :
    (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_199 F I) := by
  simpa only [nb077_alpha_dummy_198, nb077_alpha_dummy_199] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_197 (x : Var) :
    (nb077_alpha_dummy_200 x) ∉
      (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_200] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_198 (x : Var) :
    (nb077_alpha_dummy_201 x) ∉
      (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_201] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_199 (x : Var) :
    (nb077_alpha_dummy_202 x) ∉
      (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_202] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_200 (x : Var) :
    (nb077_alpha_dummy_200 x) ≠ (nb077_alpha_dummy_201 x) := by
  simpa only [nb077_alpha_dummy_200, nb077_alpha_dummy_201] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_201 (x : Var) :
    (nb077_alpha_dummy_200 x) ≠ (nb077_alpha_dummy_202 x) := by
  simpa only [nb077_alpha_dummy_200, nb077_alpha_dummy_202] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_202 (x : Var) :
    (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_202 x) := by
  simpa only [nb077_alpha_dummy_201, nb077_alpha_dummy_202] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_203 (F : Class) (I : Class) :
    (nb077_alpha_dummy_209 F I) ∉
      (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_198 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_209] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_198 F I))).fv)
      0

theorem nb077_fresh_204 (F : Class) (I : Class) :
    (nb077_alpha_dummy_205 F I) ∉
      (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_199 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_205] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_199 F I))).fv)
      0

theorem nb077_fresh_205 (F : Class) (I : Class) :
    (nb077_alpha_dummy_211 F I) ∉
      (((Class.cv (nb077_alpha_dummy_199 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_199 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_211] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_199 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_199 F I))).fv)
      0

theorem nb077_fresh_206 (x : Var) :
    (nb077_alpha_dummy_210 x) ∉
      (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_201 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_210] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_201 x))).fv)
      0

theorem nb077_fresh_207 (x : Var) :
    (nb077_alpha_dummy_206 x) ∉
      (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_206] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv)
      0

theorem nb077_fresh_208 (x : Var) :
    (nb077_alpha_dummy_212 x) ∉
      (((Class.cv (nb077_alpha_dummy_202 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_212] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_202 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv)
      0

theorem nb077_fresh_209 (F : Class) (I : Class) :
    (nb077_alpha_dummy_227 F I) ∉ (((Class.cv (nb077_alpha_dummy_220 F I))).fv) := by
  simpa only [nb077_alpha_dummy_227] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_220 F I))).fv) 0

theorem nb077_fresh_210 (F : Class) (I : Class) :
    (nb077_alpha_dummy_228 F I) ∉ (((Class.cv (nb077_alpha_dummy_220 F I))).fv) := by
  simpa only [nb077_alpha_dummy_228] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_220 F I))).fv) 1

theorem nb077_distinct_211 (F : Class) (I : Class) :
    (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_228 F I) := by
  simpa only [nb077_alpha_dummy_227, nb077_alpha_dummy_228] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_220 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_212 (x : Var) :
    (nb077_alpha_dummy_229 x) ∉ (((Class.cv (nb077_alpha_dummy_222 x))).fv) := by
  simpa only [nb077_alpha_dummy_229] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_222 x))).fv) 0

theorem nb077_fresh_213 (x : Var) :
    (nb077_alpha_dummy_230 x) ∉ (((Class.cv (nb077_alpha_dummy_222 x))).fv) := by
  simpa only [nb077_alpha_dummy_230] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_222 x))).fv) 1

theorem nb077_distinct_214 (x : Var) :
    (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_230 x) := by
  simpa only [nb077_alpha_dummy_229, nb077_alpha_dummy_230] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_222 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_215 (F : Class) (I : Class) :
    (nb077_alpha_dummy_233 F I) ∉
      (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_233] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_216 (F : Class) (I : Class) :
    (nb077_alpha_dummy_234 F I) ∉
      (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_234] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_217 (F : Class) (I : Class) :
    (nb077_alpha_dummy_235 F I) ∉
      (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_235] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_218 (F : Class) (I : Class) :
    (nb077_alpha_dummy_233 F I) ≠ (nb077_alpha_dummy_234 F I) := by
  simpa only [nb077_alpha_dummy_233, nb077_alpha_dummy_234] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part005`. -/


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

theorem nb077_distinct_219 (F : Class) (I : Class) :
    (nb077_alpha_dummy_233 F I) ≠ (nb077_alpha_dummy_235 F I) := by
  simpa only [nb077_alpha_dummy_233, nb077_alpha_dummy_235] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_220 (F : Class) (I : Class) :
    (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_235 F I) := by
  simpa only [nb077_alpha_dummy_234, nb077_alpha_dummy_235] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_221 (x : Var) :
    (nb077_alpha_dummy_236 x) ∉
      (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_236] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_222 (x : Var) :
    (nb077_alpha_dummy_237 x) ∉
      (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_237] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_223 (x : Var) :
    (nb077_alpha_dummy_238 x) ∉
      (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_238] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_224 (x : Var) :
    (nb077_alpha_dummy_236 x) ≠ (nb077_alpha_dummy_237 x) := by
  simpa only [nb077_alpha_dummy_236, nb077_alpha_dummy_237] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_225 (x : Var) :
    (nb077_alpha_dummy_236 x) ≠ (nb077_alpha_dummy_238 x) := by
  simpa only [nb077_alpha_dummy_236, nb077_alpha_dummy_238] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_226 (x : Var) :
    (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_238 x) := by
  simpa only [nb077_alpha_dummy_237, nb077_alpha_dummy_238] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_227 (F : Class) (I : Class) :
    (nb077_alpha_dummy_245 F I) ∉
      (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_234 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_245] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_234 F I))).fv)
      0

theorem nb077_fresh_228 (F : Class) (I : Class) :
    (nb077_alpha_dummy_241 F I) ∉
      (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_235 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_241] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_235 F I))).fv)
      0

theorem nb077_fresh_229 (F : Class) (I : Class) :
    (nb077_alpha_dummy_247 F I) ∉
      (((Class.cv (nb077_alpha_dummy_235 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_235 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_247] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_235 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_235 F I))).fv)
      0

theorem nb077_fresh_230 (x : Var) :
    (nb077_alpha_dummy_246 x) ∉
      (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_237 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_246] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_237 x))).fv)
      0

theorem nb077_fresh_231 (x : Var) :
    (nb077_alpha_dummy_242 x) ∉
      (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_242] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv)
      0

theorem nb077_fresh_232 (x : Var) :
    (nb077_alpha_dummy_248 x) ∉
      (((Class.cv (nb077_alpha_dummy_238 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_248] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_238 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv)
      0

theorem nb077_fresh_233 (F : Class) (I : Class) :
    (nb077_alpha_dummy_267 F I) ∉ (((Class.cv (nb077_alpha_dummy_260 F I))).fv) := by
  simpa only [nb077_alpha_dummy_267] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_260 F I))).fv) 0

theorem nb077_fresh_234 (F : Class) (I : Class) :
    (nb077_alpha_dummy_268 F I) ∉ (((Class.cv (nb077_alpha_dummy_260 F I))).fv) := by
  simpa only [nb077_alpha_dummy_268] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_260 F I))).fv) 1

theorem nb077_distinct_235 (F : Class) (I : Class) :
    (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_268 F I) := by
  simpa only [nb077_alpha_dummy_267, nb077_alpha_dummy_268] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_260 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_236 (x : Var) :
    (nb077_alpha_dummy_269 x) ∉ (((Class.cv (nb077_alpha_dummy_262 x))).fv) := by
  simpa only [nb077_alpha_dummy_269] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_262 x))).fv) 0

theorem nb077_fresh_237 (x : Var) :
    (nb077_alpha_dummy_270 x) ∉ (((Class.cv (nb077_alpha_dummy_262 x))).fv) := by
  simpa only [nb077_alpha_dummy_270] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_262 x))).fv) 1

theorem nb077_distinct_238 (x : Var) :
    (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_270 x) := by
  simpa only [nb077_alpha_dummy_269, nb077_alpha_dummy_270] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_262 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_239 (F : Class) (I : Class) :
    (nb077_alpha_dummy_273 F I) ∉
      (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_273] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_240 (F : Class) (I : Class) :
    (nb077_alpha_dummy_274 F I) ∉
      (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_274] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_241 (F : Class) (I : Class) :
    (nb077_alpha_dummy_275 F I) ∉
      (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_275] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_242 (F : Class) (I : Class) :
    (nb077_alpha_dummy_273 F I) ≠ (nb077_alpha_dummy_274 F I) := by
  simpa only [nb077_alpha_dummy_273, nb077_alpha_dummy_274] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_243 (F : Class) (I : Class) :
    (nb077_alpha_dummy_273 F I) ≠ (nb077_alpha_dummy_275 F I) := by
  simpa only [nb077_alpha_dummy_273, nb077_alpha_dummy_275] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_244 (F : Class) (I : Class) :
    (nb077_alpha_dummy_274 F I) ≠ (nb077_alpha_dummy_275 F I) := by
  simpa only [nb077_alpha_dummy_274, nb077_alpha_dummy_275] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_245 (x : Var) :
    (nb077_alpha_dummy_276 x) ∉
      (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_276] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_246 (x : Var) :
    (nb077_alpha_dummy_277 x) ∉
      (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_277] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_247 (x : Var) :
    (nb077_alpha_dummy_278 x) ∉
      (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_278] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_248 (x : Var) :
    (nb077_alpha_dummy_276 x) ≠ (nb077_alpha_dummy_277 x) := by
  simpa only [nb077_alpha_dummy_276, nb077_alpha_dummy_277] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_249 (x : Var) :
    (nb077_alpha_dummy_276 x) ≠ (nb077_alpha_dummy_278 x) := by
  simpa only [nb077_alpha_dummy_276, nb077_alpha_dummy_278] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_250 (x : Var) :
    (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_278 x) := by
  simpa only [nb077_alpha_dummy_277, nb077_alpha_dummy_278] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_251 (F : Class) (I : Class) :
    (nb077_alpha_dummy_285 F I) ∉
      (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_274 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_285] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_274 F I))).fv)
      0

theorem nb077_fresh_252 (F : Class) (I : Class) :
    (nb077_alpha_dummy_281 F I) ∉
      (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_275 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_281] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_275 F I))).fv)
      0

theorem nb077_fresh_253 (F : Class) (I : Class) :
    (nb077_alpha_dummy_287 F I) ∉
      (((Class.cv (nb077_alpha_dummy_275 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_275 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_287] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_275 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_275 F I))).fv)
      0

theorem nb077_fresh_254 (x : Var) :
    (nb077_alpha_dummy_286 x) ∉
      (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_277 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_286] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_277 x))).fv)
      0

theorem nb077_fresh_255 (x : Var) :
    (nb077_alpha_dummy_282 x) ∉
      (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_282] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv)
      0

theorem nb077_fresh_256 (x : Var) :
    (nb077_alpha_dummy_288 x) ∉
      (((Class.cv (nb077_alpha_dummy_278 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_288] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_278 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv)
      0

theorem nb077_fresh_257 (F : Class) (I : Class) :
    (nb077_alpha_dummy_307 F I) ∉
      (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_296 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_307] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_296 F I))).fv)
      0

theorem nb077_fresh_258 (F : Class) (I : Class) :
    (nb077_alpha_dummy_303 F I) ∉
      (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_297 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_303] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_297 F I))).fv)
      0

theorem nb077_fresh_259 (F : Class) (I : Class) :
    (nb077_alpha_dummy_309 F I) ∉
      (((Class.cv (nb077_alpha_dummy_297 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_297 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_309] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_297 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_297 F I))).fv)
      0

theorem nb077_fresh_260 (x : Var) :
    (nb077_alpha_dummy_308 x) ∉
      (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_299 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_308] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_299 x))).fv)
      0

theorem nb077_fresh_261 (x : Var) :
    (nb077_alpha_dummy_304 x) ∉
      (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_304] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv)
      0

theorem nb077_fresh_262 (x : Var) :
    (nb077_alpha_dummy_310 x) ∉
      (((Class.cv (nb077_alpha_dummy_300 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_310] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_300 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv)
      0

theorem nb077_fresh_263 (F : Class) (I : Class) :
    (nb077_alpha_dummy_319 F I) ∉ (((Class.cv (nb077_alpha_dummy_312 F I))).fv) := by
  simpa only [nb077_alpha_dummy_319] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_312 F I))).fv) 0

theorem nb077_fresh_264 (F : Class) (I : Class) :
    (nb077_alpha_dummy_320 F I) ∉ (((Class.cv (nb077_alpha_dummy_312 F I))).fv) := by
  simpa only [nb077_alpha_dummy_320] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_312 F I))).fv) 1

theorem nb077_distinct_265 (F : Class) (I : Class) :
    (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_320 F I) := by
  simpa only [nb077_alpha_dummy_319, nb077_alpha_dummy_320] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_312 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_266 (x : Var) :
    (nb077_alpha_dummy_321 x) ∉ (((Class.cv (nb077_alpha_dummy_314 x))).fv) := by
  simpa only [nb077_alpha_dummy_321] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_314 x))).fv) 0

theorem nb077_fresh_267 (x : Var) :
    (nb077_alpha_dummy_322 x) ∉ (((Class.cv (nb077_alpha_dummy_314 x))).fv) := by
  simpa only [nb077_alpha_dummy_322] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_314 x))).fv) 1

theorem nb077_distinct_268 (x : Var) :
    (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_322 x) := by
  simpa only [nb077_alpha_dummy_321, nb077_alpha_dummy_322] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_314 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_269 (F : Class) (I : Class) :
    (nb077_alpha_dummy_325 F I) ∉
      (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_325] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_270 (F : Class) (I : Class) :
    (nb077_alpha_dummy_326 F I) ∉
      (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_326] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_271 (F : Class) (I : Class) :
    (nb077_alpha_dummy_327 F I) ∉
      (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_327] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_272 (F : Class) (I : Class) :
    (nb077_alpha_dummy_325 F I) ≠ (nb077_alpha_dummy_326 F I) := by
  simpa only [nb077_alpha_dummy_325, nb077_alpha_dummy_326] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_273 (F : Class) (I : Class) :
    (nb077_alpha_dummy_325 F I) ≠ (nb077_alpha_dummy_327 F I) := by
  simpa only [nb077_alpha_dummy_325, nb077_alpha_dummy_327] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_274 (F : Class) (I : Class) :
    (nb077_alpha_dummy_326 F I) ≠ (nb077_alpha_dummy_327 F I) := by
  simpa only [nb077_alpha_dummy_326, nb077_alpha_dummy_327] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_275 (x : Var) :
    (nb077_alpha_dummy_328 x) ∉
      (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_328] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_276 (x : Var) :
    (nb077_alpha_dummy_329 x) ∉
      (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_329] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_277 (x : Var) :
    (nb077_alpha_dummy_330 x) ∉
      (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb077_alpha_dummy_330] using
    freshVar_not_mem (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_278 (x : Var) :
    (nb077_alpha_dummy_328 x) ≠ (nb077_alpha_dummy_329 x) := by
  simpa only [nb077_alpha_dummy_328, nb077_alpha_dummy_329] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_279 (x : Var) :
    (nb077_alpha_dummy_328 x) ≠ (nb077_alpha_dummy_330 x) := by
  simpa only [nb077_alpha_dummy_328, nb077_alpha_dummy_330] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_280 (x : Var) :
    (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_330 x) := by
  simpa only [nb077_alpha_dummy_329, nb077_alpha_dummy_330] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_281 (F : Class) (I : Class) :
    (nb077_alpha_dummy_337 F I) ∉
      (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_326 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_337] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_326 F I))).fv)
      0

theorem nb077_fresh_282 (F : Class) (I : Class) :
    (nb077_alpha_dummy_333 F I) ∉
      (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_327 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_333] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_327 F I))).fv)
      0

theorem nb077_fresh_283 (F : Class) (I : Class) :
    (nb077_alpha_dummy_339 F I) ∉
      (((Class.cv (nb077_alpha_dummy_327 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_327 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_339] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_327 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_327 F I))).fv)
      0

theorem nb077_fresh_284 (x : Var) :
    (nb077_alpha_dummy_338 x) ∉
      (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_329 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_338] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_329 x))).fv)
      0

theorem nb077_fresh_285 (x : Var) :
    (nb077_alpha_dummy_334 x) ∉
      (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_334] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv)
      0

theorem nb077_fresh_286 (x : Var) :
    (nb077_alpha_dummy_340 x) ∉
      (((Class.cv (nb077_alpha_dummy_330 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_340] using
    freshVar_not_mem
      (((Class.cv (nb077_alpha_dummy_330 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv)
      0

theorem nb077_fresh_287 (x : Var) :
    (nb077_alpha_dummy_261 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_261] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) 0

theorem nb077_fresh_288 (x : Var) :
    (nb077_alpha_dummy_262 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_262] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) 1

theorem nb077_distinct_289 (x : Var) :
    (nb077_alpha_dummy_261 x) ≠ (nb077_alpha_dummy_262 x) := by
  simpa only [nb077_alpha_dummy_261, nb077_alpha_dummy_262] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_fresh_290 (x : Var) :
    (nb077_alpha_dummy_298 x) ∉ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_298] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_291 (x : Var) :
    (nb077_alpha_dummy_299 x) ∉ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_299] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_292 (x : Var) :
    (nb077_alpha_dummy_300 x) ∉ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_300] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_293 (x : Var) :
    (nb077_alpha_dummy_298 x) ≠ (nb077_alpha_dummy_299 x) := by
  simpa only [nb077_alpha_dummy_298, nb077_alpha_dummy_299] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_294 (x : Var) :
    (nb077_alpha_dummy_298 x) ≠ (nb077_alpha_dummy_300 x) := by
  simpa only [nb077_alpha_dummy_298, nb077_alpha_dummy_300] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_295 (x : Var) :
    (nb077_alpha_dummy_299 x) ≠ (nb077_alpha_dummy_300 x) := by
  simpa only [nb077_alpha_dummy_299, nb077_alpha_dummy_300] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_296 (F : Class) (I : Class) :
    (nb077_alpha_dummy_031 F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_027 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_027 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_027 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_031] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_027 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_027 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_027 F I))).fv)
      0

theorem nb077_fresh_297 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_032 x F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_029 x F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_032] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_029 x F I))).fv)
      0

theorem nb077_fresh_298 (F : Class) (I : Class) :
    (nb077_alpha_dummy_079 F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_075 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_075 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_075 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_079] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_075 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_075 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_075 F I))).fv)
      0

theorem nb077_fresh_299 (x : Var) :
    (nb077_alpha_dummy_080 x) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_077 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_077 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_077 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_080] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_077 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_077 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_077 x))).fv)
      0

theorem nb077_fresh_300 (F : Class) (I : Class) :
    (nb077_alpha_dummy_115 F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_111 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_111 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_111 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_115] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_111 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_111 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_111 F I))).fv)
      0

theorem nb077_fresh_301 (x : Var) :
    (nb077_alpha_dummy_116 x) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_113 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_113 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_113 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_116] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_113 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_113 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_113 x))).fv)
      0

theorem nb077_fresh_302 (F : Class) (I : Class) :
    (nb077_alpha_dummy_159 F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_155 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_155 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_155 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_159] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_155 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_155 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_155 F I))).fv)
      0

theorem nb077_fresh_303 (x : Var) :
    (nb077_alpha_dummy_160 x) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_157 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_157 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_157 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_160] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_157 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_157 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_157 x))).fv)
      0

theorem nb077_fresh_304 (F : Class) (I : Class) :
    (nb077_alpha_dummy_195 F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_191 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_191 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_191 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_195] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_191 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_191 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_191 F I))).fv)
      0

theorem nb077_fresh_305 (x : Var) :
    (nb077_alpha_dummy_196 x) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_193 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_193 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_193 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_196] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_193 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_193 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_193 x))).fv)
      0

theorem nb077_fresh_306 (F : Class) (I : Class) :
    (nb077_alpha_dummy_231 F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_227 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_227 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_227 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_231] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_227 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_227 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_227 F I))).fv)
      0

theorem nb077_fresh_307 (x : Var) :
    (nb077_alpha_dummy_232 x) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_229 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_229 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_229 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_232] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_229 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_229 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_229 x))).fv)
      0

theorem nb077_fresh_308 (F : Class) (I : Class) :
    (nb077_alpha_dummy_271 F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_267 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_267 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_267 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_271] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_267 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_267 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_267 F I))).fv)
      0

theorem nb077_fresh_309 (x : Var) :
    (nb077_alpha_dummy_272 x) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_269 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_269 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_269 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_272] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_269 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_269 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_269 x))).fv)
      0

theorem nb077_fresh_310 (F : Class) (I : Class) :
    (nb077_alpha_dummy_323 F I) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_319 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_319 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_319 F I))).fv) :=
  by
  simpa only [nb077_alpha_dummy_323] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_319 F I)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_319 F I)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_319 F I))).fv)
      0

theorem nb077_fresh_311 (x : Var) :
    (nb077_alpha_dummy_324 x) ∉
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_321 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_321 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_321 x))).fv) :=
  by
  simpa only [nb077_alpha_dummy_324] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077_alpha_dummy_321 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb077_alpha_dummy_321 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb077_alpha_dummy_321 x))).fv)
      0

theorem nb077_fresh_312 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∉
      (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) :=
  by
  simpa only [nb077_alpha_dummy_059] using
    freshVar_not_mem
      (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv)
      0

theorem nb077_fresh_313 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ∉
      (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) :=
  by
  simpa only [nb077_alpha_dummy_060] using
    freshVar_not_mem
      (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv)
      1

theorem nb077_fresh_314 (F : Class) (I : Class) :
    (nb077_alpha_dummy_061 F I) ∉
      (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) :=
  by
  simpa only [nb077_alpha_dummy_061] using
    freshVar_not_mem
      (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv)
      2

theorem nb077_distinct_315 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_060 F I) := by
  simpa only [nb077_alpha_dummy_059, nb077_alpha_dummy_060] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
            (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_316 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_061 F I) := by
  simpa only [nb077_alpha_dummy_059, nb077_alpha_dummy_061] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
            (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_317 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_061 F I) := by
  simpa only [nb077_alpha_dummy_060, nb077_alpha_dummy_061] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
            (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_318 (x : Var) :
    (nb077_alpha_dummy_062 x) ∉
      (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) :=
  by
  simpa only [nb077_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv)
      0

theorem nb077_fresh_319 (x : Var) :
    (nb077_alpha_dummy_063 x) ∉
      (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) :=
  by
  simpa only [nb077_alpha_dummy_063] using
    freshVar_not_mem
      (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv)
      1

theorem nb077_fresh_320 (x : Var) :
    (nb077_alpha_dummy_064 x) ∉
      (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) :=
  by
  simpa only [nb077_alpha_dummy_064] using
    freshVar_not_mem
      (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv)
      2

theorem nb077_distinct_321 (x : Var) :
    (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_063 x) := by
  simpa only [nb077_alpha_dummy_062, nb077_alpha_dummy_063] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_322 (x : Var) :
    (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_064 x) := by
  simpa only [nb077_alpha_dummy_062, nb077_alpha_dummy_064] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_323 (x : Var) :
    (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_064 x) := by
  simpa only [nb077_alpha_dummy_063, nb077_alpha_dummy_064] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_324 (F : Class) (I : Class) :
    (nb077_alpha_dummy_057 F I) ∉
      (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))).fv ∪
        ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_057] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))).fv ∪
        ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv)
      0

theorem nb077_fresh_325 (x : Var) (F : Class) :
    (nb077_alpha_dummy_058 x F) ∉
      (((syn_ccom (syn_ccnv (syn_c1st))
            (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
              (syn_c1st)))).fv ∪
        ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_058] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (syn_c1st))
            (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
              (syn_c1st)))).fv ∪ ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv)
      0

theorem nb077_fresh_326 (F : Class) (I : Class) :
    (nb077_alpha_dummy_023 F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_023] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_327 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_024 x F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I)
              (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
                (Class.cv (nb077_alpha_dummy_017 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_024] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I)
              (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
                (Class.cv (nb077_alpha_dummy_017 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_328 (F : Class) (I : Class) :
    (nb077_alpha_dummy_071 F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_071] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_329 (x : Var) :
    (nb077_alpha_dummy_072 x) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_072] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_330 (F : Class) (I : Class) :
    (nb077_alpha_dummy_107 F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_107] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_331 (x : Var) :
    (nb077_alpha_dummy_108 x) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_108] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_332 (F : Class) (I : Class) :
    (nb077_alpha_dummy_151 F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_333 (x : Var) :
    (nb077_alpha_dummy_152 x) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_334 (F : Class) (I : Class) :
    (nb077_alpha_dummy_187 F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_187] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_335 (x : Var) :
    (nb077_alpha_dummy_188 x) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_188] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_336 (F : Class) (I : Class) :
    (nb077_alpha_dummy_223 F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_223] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_337 (x : Var) :
    (nb077_alpha_dummy_224 x) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_224] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_338 (F : Class) (I : Class) :
    (nb077_alpha_dummy_263 F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_263] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_339 (x : Var) :
    (nb077_alpha_dummy_264 x) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_264] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_340 (F : Class) (I : Class) :
    (nb077_alpha_dummy_315 F I) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I)
              (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_311 F I)
              (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_315] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I)
              (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_311 F I)
              (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_341 (x : Var) :
    (nb077_alpha_dummy_316 x) ∉
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x)
              (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_313 x)
              (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb077_alpha_dummy_316] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x)
              (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb077_alpha_dummy_313 x)
              (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                  (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb077_fresh_342 (F : Class) (I : Class) :
    (nb077_alpha_dummy_043 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv)
      0

theorem nb077_fresh_343 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_044 x F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv)
      0

theorem nb077_fresh_344 (F : Class) (I : Class) :
    (nb077_alpha_dummy_091 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_091] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv)
      0

theorem nb077_fresh_345 (x : Var) :
    (nb077_alpha_dummy_092 x) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_092] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv)
      0

theorem nb077_fresh_346 (F : Class) (I : Class) :
    (nb077_alpha_dummy_127 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_127] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv)
      0

theorem nb077_fresh_347 (x : Var) :
    (nb077_alpha_dummy_128 x) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_128] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv)
      0

theorem nb077_fresh_348 (F : Class) (I : Class) :
    (nb077_alpha_dummy_171 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_171] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv)
      0

theorem nb077_fresh_349 (x : Var) :
    (nb077_alpha_dummy_172 x) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_172] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv)
      0

theorem nb077_fresh_350 (F : Class) (I : Class) :
    (nb077_alpha_dummy_207 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_207] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv)
      0

theorem nb077_fresh_351 (x : Var) :
    (nb077_alpha_dummy_208 x) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_208] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv)
      0

theorem nb077_fresh_352 (F : Class) (I : Class) :
    (nb077_alpha_dummy_243 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_243] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv)
      0

theorem nb077_fresh_353 (x : Var) :
    (nb077_alpha_dummy_244 x) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_244] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv)
      0

theorem nb077_fresh_354 (F : Class) (I : Class) :
    (nb077_alpha_dummy_283 F I) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_283] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv)
      0

theorem nb077_fresh_355 (x : Var) :
    (nb077_alpha_dummy_284 x) ∉
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) :=
  by
  simpa only [nb077_alpha_dummy_284] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
