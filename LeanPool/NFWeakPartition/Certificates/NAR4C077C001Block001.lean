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

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_000`. -/
@[expose]
noncomputable def nb077AlphaDummy000 (F : Class) (I : Class) : Var :=
  (freshVar ((F).fv ∪ (I).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_001`. -/
@[expose]
noncomputable def nb077AlphaDummy001 (F : Class) (I : Class) : Var :=
  (freshVar (((synCsn (synCop (synC0c) I))).fv ∪ ((synCpprod
          (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_002`. -/
@[expose]
noncomputable def nb077AlphaDummy002 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCsn (synCop (synC0c) I))).fv ∪
      ((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_003`. -/
@[expose]
noncomputable def nb077AlphaDummy003 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy001 F I) (synWa
          (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
          (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))
            (Class.cv (nb077AlphaDummy001 F I)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_004`. -/
@[expose]
noncomputable def nb077AlphaDummy004 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy001 F I) (synWa
          (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
          (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
              (Class.cv (nb077AlphaDummy001 F I)))
            (Class.cv (nb077AlphaDummy001 F I)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_005`. -/
@[expose]
noncomputable def nb077AlphaDummy005 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy002 x F I) (synWa
          (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
          (synWss (synCima
              (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))
            (Class.cv (nb077AlphaDummy002 x F I)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_006`. -/
@[expose]
noncomputable def nb077AlphaDummy006 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy002 x F I) (synWa
          (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
          (synWss (synCima
              (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
              (Class.cv (nb077AlphaDummy002 x F I)))
            (Class.cv (nb077AlphaDummy002 x F I)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_007`. -/
@[expose]
noncomputable def nb077AlphaDummy007 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (synCsn (synCop (synC0c) I))
          (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
      ((synCnin (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_008`. -/
@[expose]
noncomputable def nb077AlphaDummy008 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (synCsn (synCop (synC0c) I))
          (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
      ((synCnin (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_009`. -/
@[expose]
noncomputable def nb077AlphaDummy009 (F : Class) (I : Class) : Var :=
  (freshVar (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_010`. -/
@[expose]
noncomputable def nb077AlphaDummy010 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar
    (((synCsn (synCop (synC0c) I))).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_011`. -/
@[expose]
noncomputable def nb077AlphaDummy011 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I)))
          (Class.cv (nb077AlphaDummy001 F I)))).fv ∪ ((synCnin (synCima (synCpprod
              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
            (Class.cv (nb077AlphaDummy001 F I))) (Class.cv (nb077AlphaDummy001 F I)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_012`. -/
@[expose]
noncomputable def nb077AlphaDummy012 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))
          (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪ ((synCnin (synCima
            (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
            (Class.cv (nb077AlphaDummy002 x F I)))
          (Class.cv (nb077AlphaDummy002 x F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_013`. -/
@[expose]
noncomputable def nb077AlphaDummy013 (F : Class) (I : Class) : Var :=
  (freshVar (((synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
          (Class.cv (nb077AlphaDummy001 F I)))).fv ∪
      ((Class.cv (nb077AlphaDummy001 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_014`. -/
@[expose]
noncomputable def nb077AlphaDummy014 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCima (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
          (Class.cv (nb077AlphaDummy002 x F I)))).fv ∪
      ((Class.cv (nb077AlphaDummy002 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_015`. -/
@[expose]
noncomputable def nb077AlphaDummy015 (F : Class) (I : Class) : Var :=
  (freshVar (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
      ((Class.cv (nb077AlphaDummy001 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_016`. -/
@[expose]
noncomputable def nb077AlphaDummy016 (F : Class) (I : Class) : Var :=
  (freshVar (((synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)).fv ∪
      ((Class.cv (nb077AlphaDummy001 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_017`. -/
@[expose]
noncomputable def nb077AlphaDummy017 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
      ((Class.cv (nb077AlphaDummy002 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_018`. -/
@[expose]
noncomputable def nb077AlphaDummy018 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)).fv ∪
      ((Class.cv (nb077AlphaDummy002 x F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_019`. -/
@[expose]
noncomputable def nb077AlphaDummy019 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy015 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_020`. -/
@[expose]
noncomputable def nb077AlphaDummy020 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy015 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_021`. -/
@[expose]
noncomputable def nb077AlphaDummy021 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
      ((Class.cv (nb077AlphaDummy017 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_022`. -/
@[expose]
noncomputable def nb077AlphaDummy022 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
      ((Class.cv (nb077AlphaDummy017 x F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_023`. -/
@[expose]
noncomputable def nb077AlphaDummy023 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCphi (Class.cv (nb077AlphaDummy020 F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_024`. -/
@[expose]
noncomputable def nb077AlphaDummy024 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy021 x F I)
            (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy018 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCphi (Class.cv (nb077AlphaDummy022 x F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy017 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_025`. -/
@[expose]
noncomputable def nb077AlphaDummy025 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy019 F I)
          (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
              (synCphi (Class.cv (nb077AlphaDummy020 F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy019 F I)
          (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
              (synCphi (Class.cv (nb077AlphaDummy020 F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_026`. -/
@[expose]
noncomputable def nb077AlphaDummy026 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy021 x F I)
          (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy018 x F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
              (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy021 x F I)
          (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy018 x F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
              (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_027`. -/
@[expose]
noncomputable def nb077AlphaDummy027 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy020 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_028`. -/
@[expose]
noncomputable def nb077AlphaDummy028 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy020 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_029`. -/
@[expose]
noncomputable def nb077AlphaDummy029 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy022 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_030`. -/
@[expose]
noncomputable def nb077AlphaDummy030 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy022 x F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_031`. -/
@[expose]
noncomputable def nb077AlphaDummy031 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy027 F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy027 F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy027 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_032`. -/
@[expose]
noncomputable def nb077AlphaDummy032 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy029 x F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy029 x F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy029 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_033`. -/
@[expose]
noncomputable def nb077AlphaDummy033 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_034`. -/
@[expose]
noncomputable def nb077AlphaDummy034 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_035`. -/
@[expose]
noncomputable def nb077AlphaDummy035 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_036`. -/
@[expose]
noncomputable def nb077AlphaDummy036 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_037`. -/
@[expose]
noncomputable def nb077AlphaDummy037 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_038`. -/
@[expose]
noncomputable def nb077AlphaDummy038 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_039`. -/
@[expose]
noncomputable def nb077AlphaDummy039 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy034 F I))
          (Class.cv (nb077AlphaDummy035 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy034 F I))
          (Class.cv (nb077AlphaDummy035 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_040`. -/
@[expose]
noncomputable def nb077AlphaDummy040 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy037 x F I))
          (Class.cv (nb077AlphaDummy038 x F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy037 x F I))
          (Class.cv (nb077AlphaDummy038 x F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_041`. -/
@[expose]
noncomputable def nb077AlphaDummy041 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy035 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_042`. -/
@[expose]
noncomputable def nb077AlphaDummy042 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
      ((Class.cv (nb077AlphaDummy038 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_043`. -/
@[expose]
noncomputable def nb077AlphaDummy043 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy034 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy035 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_044`. -/
@[expose]
noncomputable def nb077AlphaDummy044 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy037 x F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy038 x F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_045`. -/
@[expose]
noncomputable def nb077AlphaDummy045 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy034 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_046`. -/
@[expose]
noncomputable def nb077AlphaDummy046 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
      ((Class.cv (nb077AlphaDummy037 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_047`. -/
@[expose]
noncomputable def nb077AlphaDummy047 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy035 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy035 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_048`. -/
@[expose]
noncomputable def nb077AlphaDummy048 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy038 x F I))).fv ∪
      ((Class.cv (nb077AlphaDummy038 x F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_049`. -/
@[expose]
noncomputable def nb077AlphaDummy049 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy019 F I)
          (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy019 F I)
          (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_050`. -/
@[expose]
noncomputable def nb077AlphaDummy050 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy021 x F I)
          (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy017 x F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy021 x F I)
          (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy017 x F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_051`. -/
@[expose]
noncomputable def nb077AlphaDummy051 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy020 F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_052`. -/
@[expose]
noncomputable def nb077AlphaDummy052 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy022 x F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_053`. -/
@[expose]
noncomputable def nb077AlphaDummy053 (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy020 F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy020 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_054`. -/
@[expose]
noncomputable def nb077AlphaDummy054 (x : Var) (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy022 x F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy022 x F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_055`. -/
@[expose]
noncomputable def nb077AlphaDummy055 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (synC1st)) (synCcom
              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
          (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv ∪ ((synCnin
          (synCcom (synCcnv (synC1st)) (synCcom
              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
          (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_056`. -/
@[expose]
noncomputable def nb077AlphaDummy056 (x : Var) (F : Class) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (synC1st))
            (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
          (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv ∪ ((synCnin
          (synCcom (synCcnv (synC1st))
            (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
          (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_057`. -/
@[expose]
noncomputable def nb077AlphaDummy057 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcom (synCcnv (synC1st)) (synCcom
            (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))).fv ∪
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_058`. -/
@[expose]
noncomputable def nb077AlphaDummy058 (x : Var) (F : Class) : Var :=
  (freshVar (((synCcom (synCcnv (synC1st))
          (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))).fv ∪
      ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_059`. -/
@[expose]
noncomputable def nb077AlphaDummy059 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcnv (synC1st))).fv ∪ ((synCcom
          (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_060`. -/
@[expose]
noncomputable def nb077AlphaDummy060 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcnv (synC1st))).fv ∪ ((synCcom
          (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_061`. -/
@[expose]
noncomputable def nb077AlphaDummy061 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcnv (synC1st))).fv ∪ ((synCcom
          (synCmpt (nb077AlphaDummy000 F I) (synCvv)
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_062`. -/
@[expose]
noncomputable def nb077AlphaDummy062 (x : Var) : Var :=
  (freshVar (((synCcnv (synC1st))).fv ∪
      ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_063`. -/
@[expose]
noncomputable def nb077AlphaDummy063 (x : Var) : Var :=
  (freshVar (((synCcnv (synC1st))).fv ∪
      ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_064`. -/
@[expose]
noncomputable def nb077AlphaDummy064 (x : Var) : Var :=
  (freshVar (((synCcnv (synC1st))).fv ∪
      ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_065`. -/
@[expose]
noncomputable def nb077AlphaDummy065 (F : Class) (I : Class) : Var :=
  (freshVar (({(nb077AlphaDummy059 F I)} : Finset Var) ∪
        ({(nb077AlphaDummy060 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy061 F I)
          (synWa (synWbr (Class.cv (nb077AlphaDummy059 F I)) (synCcom
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))
              (Class.cv (nb077AlphaDummy061 F I)))
            (synWbr (Class.cv (nb077AlphaDummy061 F I)) (synCcnv (synC1st))
              (Class.cv (nb077AlphaDummy060 F I)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_066`. -/
@[expose]
noncomputable def nb077AlphaDummy066 (x : Var) : Var :=
  (freshVar (({(nb077AlphaDummy062 x)} : Finset Var) ∪
        ({(nb077AlphaDummy063 x)} : Finset Var) ∪ ((synWex (nb077AlphaDummy064 x) (synWa
            (synWbr (Class.cv (nb077AlphaDummy062 x))
              (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))
              (Class.cv (nb077AlphaDummy064 x)))
            (synWbr (Class.cv (nb077AlphaDummy064 x)) (synCcnv (synC1st))
              (Class.cv (nb077AlphaDummy063 x)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_067`. -/
@[expose]
noncomputable def nb077AlphaDummy067 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy060 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_068`. -/
@[expose]
noncomputable def nb077AlphaDummy068 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy060 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_069`. -/
@[expose]
noncomputable def nb077AlphaDummy069 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy062 x))).fv ∪
      ((Class.cv (nb077AlphaDummy063 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_070`. -/
@[expose]
noncomputable def nb077AlphaDummy070 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy062 x))).fv ∪
      ((Class.cv (nb077AlphaDummy063 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_071`. -/
@[expose]
noncomputable def nb077AlphaDummy071 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCphi (Class.cv (nb077AlphaDummy068 F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_072`. -/
@[expose]
noncomputable def nb077AlphaDummy072 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCphi (Class.cv (nb077AlphaDummy070 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_073`. -/
@[expose]
noncomputable def nb077AlphaDummy073 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy067 F I)
          (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
              (synCphi (Class.cv (nb077AlphaDummy068 F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy067 F I)
          (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
              (synCphi (Class.cv (nb077AlphaDummy068 F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_074`. -/
@[expose]
noncomputable def nb077AlphaDummy074 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy069 x)
          (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
              (synCphi (Class.cv (nb077AlphaDummy070 x))))))).fv ∪
      ((Class.cab (nb077AlphaDummy069 x)
          (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
              (synCphi (Class.cv (nb077AlphaDummy070 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_075`. -/
@[expose]
noncomputable def nb077AlphaDummy075 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy068 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_076`. -/
@[expose]
noncomputable def nb077AlphaDummy076 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy068 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_077`. -/
@[expose]
noncomputable def nb077AlphaDummy077 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy070 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_078`. -/
@[expose]
noncomputable def nb077AlphaDummy078 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy070 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_079`. -/
@[expose]
noncomputable def nb077AlphaDummy079 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy075 F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy075 F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy075 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_080`. -/
@[expose]
noncomputable def nb077AlphaDummy080 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy077 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy077 x)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy077 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_081`. -/
@[expose]
noncomputable def nb077AlphaDummy081 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_082`. -/
@[expose]
noncomputable def nb077AlphaDummy082 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_083`. -/
@[expose]
noncomputable def nb077AlphaDummy083 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_084`. -/
@[expose]
noncomputable def nb077AlphaDummy084 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_085`. -/
@[expose]
noncomputable def nb077AlphaDummy085 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_086`. -/
@[expose]
noncomputable def nb077AlphaDummy086 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_087`. -/
@[expose]
noncomputable def nb077AlphaDummy087 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy082 F I))
          (Class.cv (nb077AlphaDummy083 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy082 F I))
          (Class.cv (nb077AlphaDummy083 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_088`. -/
@[expose]
noncomputable def nb077AlphaDummy088 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy085 x))
          (Class.cv (nb077AlphaDummy086 x)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy085 x)) (Class.cv (nb077AlphaDummy086 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_089`. -/
@[expose]
noncomputable def nb077AlphaDummy089 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy083 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_090`. -/
@[expose]
noncomputable def nb077AlphaDummy090 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy085 x))).fv ∪
      ((Class.cv (nb077AlphaDummy086 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_091`. -/
@[expose]
noncomputable def nb077AlphaDummy091 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy082 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy083 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_092`. -/
@[expose]
noncomputable def nb077AlphaDummy092 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy085 x)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy086 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_093`. -/
@[expose]
noncomputable def nb077AlphaDummy093 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy082 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_094`. -/
@[expose]
noncomputable def nb077AlphaDummy094 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy085 x))).fv ∪
      ((Class.cv (nb077AlphaDummy085 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_095`. -/
@[expose]
noncomputable def nb077AlphaDummy095 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy083 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy083 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_096`. -/
@[expose]
noncomputable def nb077AlphaDummy096 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy086 x))).fv ∪
      ((Class.cv (nb077AlphaDummy086 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_097`. -/
@[expose]
noncomputable def nb077AlphaDummy097 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy067 F I)
          (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy067 F I)
          (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_098`. -/
@[expose]
noncomputable def nb077AlphaDummy098 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy069 x)
          (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy069 x)
          (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_099`. -/
@[expose]
noncomputable def nb077AlphaDummy099 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy068 F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_100`. -/
@[expose]
noncomputable def nb077AlphaDummy100 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy070 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_101`. -/
@[expose]
noncomputable def nb077AlphaDummy101 (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy068 F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy068 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_102`. -/
@[expose]
noncomputable def nb077AlphaDummy102 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy070 x)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy070 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_103`. -/
@[expose]
noncomputable def nb077AlphaDummy103 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy061 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_104`. -/
@[expose]
noncomputable def nb077AlphaDummy104 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy061 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_105`. -/
@[expose]
noncomputable def nb077AlphaDummy105 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy062 x))).fv ∪
      ((Class.cv (nb077AlphaDummy064 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_106`. -/
@[expose]
noncomputable def nb077AlphaDummy106 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy062 x))).fv ∪
      ((Class.cv (nb077AlphaDummy064 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_107`. -/
@[expose]
noncomputable def nb077AlphaDummy107 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCphi (Class.cv (nb077AlphaDummy104 F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_108`. -/
@[expose]
noncomputable def nb077AlphaDummy108 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCphi (Class.cv (nb077AlphaDummy106 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_109`. -/
@[expose]
noncomputable def nb077AlphaDummy109 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy103 F I)
          (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
              (synCphi (Class.cv (nb077AlphaDummy104 F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy103 F I)
          (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
              (synCphi (Class.cv (nb077AlphaDummy104 F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_110`. -/
@[expose]
noncomputable def nb077AlphaDummy110 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy105 x)
          (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
              (synCphi (Class.cv (nb077AlphaDummy106 x))))))).fv ∪
      ((Class.cab (nb077AlphaDummy105 x)
          (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
              (synCphi (Class.cv (nb077AlphaDummy106 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_111`. -/
@[expose]
noncomputable def nb077AlphaDummy111 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy104 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_112`. -/
@[expose]
noncomputable def nb077AlphaDummy112 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy104 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_113`. -/
@[expose]
noncomputable def nb077AlphaDummy113 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy106 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_114`. -/
@[expose]
noncomputable def nb077AlphaDummy114 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy106 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_115`. -/
@[expose]
noncomputable def nb077AlphaDummy115 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy111 F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy111 F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy111 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_116`. -/
@[expose]
noncomputable def nb077AlphaDummy116 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy113 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy113 x)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy113 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_117`. -/
@[expose]
noncomputable def nb077AlphaDummy117 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_118`. -/
@[expose]
noncomputable def nb077AlphaDummy118 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_119`. -/
@[expose]
noncomputable def nb077AlphaDummy119 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_120`. -/
@[expose]
noncomputable def nb077AlphaDummy120 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_121`. -/
@[expose]
noncomputable def nb077AlphaDummy121 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_122`. -/
@[expose]
noncomputable def nb077AlphaDummy122 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_123`. -/
@[expose]
noncomputable def nb077AlphaDummy123 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy118 F I))
          (Class.cv (nb077AlphaDummy119 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy118 F I))
          (Class.cv (nb077AlphaDummy119 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_124`. -/
@[expose]
noncomputable def nb077AlphaDummy124 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy121 x))
          (Class.cv (nb077AlphaDummy122 x)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy121 x)) (Class.cv (nb077AlphaDummy122 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_125`. -/
@[expose]
noncomputable def nb077AlphaDummy125 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy119 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_126`. -/
@[expose]
noncomputable def nb077AlphaDummy126 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy121 x))).fv ∪
      ((Class.cv (nb077AlphaDummy122 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_127`. -/
@[expose]
noncomputable def nb077AlphaDummy127 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy118 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy119 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_128`. -/
@[expose]
noncomputable def nb077AlphaDummy128 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy121 x)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy122 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_129`. -/
@[expose]
noncomputable def nb077AlphaDummy129 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy118 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_130`. -/
@[expose]
noncomputable def nb077AlphaDummy130 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy121 x))).fv ∪
      ((Class.cv (nb077AlphaDummy121 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_131`. -/
@[expose]
noncomputable def nb077AlphaDummy131 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy119 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy119 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_132`. -/
@[expose]
noncomputable def nb077AlphaDummy132 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy122 x))).fv ∪
      ((Class.cv (nb077AlphaDummy122 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_133`. -/
@[expose]
noncomputable def nb077AlphaDummy133 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy103 F I)
          (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy103 F I)
          (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_134`. -/
@[expose]
noncomputable def nb077AlphaDummy134 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy105 x)
          (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy105 x)
          (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_135`. -/
@[expose]
noncomputable def nb077AlphaDummy135 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy104 F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_136`. -/
@[expose]
noncomputable def nb077AlphaDummy136 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy106 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_137`. -/
@[expose]
noncomputable def nb077AlphaDummy137 (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy104 F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy104 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_138`. -/
@[expose]
noncomputable def nb077AlphaDummy138 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy106 x)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy106 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_139`. -/
@[expose]
noncomputable def nb077AlphaDummy139 (F : Class) (I : Class) : Var :=
  (freshVar (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
          (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_140`. -/
@[expose]
noncomputable def nb077AlphaDummy140 (F : Class) (I : Class) : Var :=
  (freshVar (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
          (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_141`. -/
@[expose]
noncomputable def nb077AlphaDummy141 (F : Class) (I : Class) : Var :=
  (freshVar (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
          (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))).fv ∪ ((synC1st)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_142`. -/
@[expose]
noncomputable def nb077AlphaDummy142 (x : Var) : Var :=
  (freshVar (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_143`. -/
@[expose]
noncomputable def nb077AlphaDummy143 (x : Var) : Var :=
  (freshVar (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_144`. -/
@[expose]
noncomputable def nb077AlphaDummy144 (x : Var) : Var :=
  (freshVar (((synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_145`. -/
@[expose]
noncomputable def nb077AlphaDummy145 (F : Class) (I : Class) : Var :=
  (freshVar (({(nb077AlphaDummy139 F I)} : Finset Var) ∪
        ({(nb077AlphaDummy140 F I)} : Finset Var) ∪ ((synWex (nb077AlphaDummy141 F I)
          (synWa (synWbr (Class.cv (nb077AlphaDummy139 F I)) (synC1st)
              (Class.cv (nb077AlphaDummy141 F I)))
            (synWbr (Class.cv (nb077AlphaDummy141 F I))
              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
              (Class.cv (nb077AlphaDummy140 F I)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_146`. -/
@[expose]
noncomputable def nb077AlphaDummy146 (x : Var) : Var :=
  (freshVar (({(nb077AlphaDummy142 x)} : Finset Var) ∪
        ({(nb077AlphaDummy143 x)} : Finset Var) ∪ ((synWex (nb077AlphaDummy144 x) (synWa
            (synWbr (Class.cv (nb077AlphaDummy142 x)) (synC1st)
              (Class.cv (nb077AlphaDummy144 x)))
            (synWbr (Class.cv (nb077AlphaDummy144 x))
              (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
              (Class.cv (nb077AlphaDummy143 x)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_147`. -/
@[expose]
noncomputable def nb077AlphaDummy147 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy140 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_148`. -/
@[expose]
noncomputable def nb077AlphaDummy148 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy140 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_149`. -/
@[expose]
noncomputable def nb077AlphaDummy149 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy142 x))).fv ∪
      ((Class.cv (nb077AlphaDummy143 x))).fv) 0)

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

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_150`. -/
@[expose]
noncomputable def nb077AlphaDummy150 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy142 x))).fv ∪
      ((Class.cv (nb077AlphaDummy143 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_151`. -/
@[expose]
noncomputable def nb077AlphaDummy151 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCphi (Class.cv (nb077AlphaDummy148 F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_152`. -/
@[expose]
noncomputable def nb077AlphaDummy152 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCphi (Class.cv (nb077AlphaDummy150 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_153`. -/
@[expose]
noncomputable def nb077AlphaDummy153 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy147 F I)
          (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
              (synCphi (Class.cv (nb077AlphaDummy148 F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy147 F I)
          (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
              (synCphi (Class.cv (nb077AlphaDummy148 F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_154`. -/
@[expose]
noncomputable def nb077AlphaDummy154 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy149 x)
          (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
              (synCphi (Class.cv (nb077AlphaDummy150 x))))))).fv ∪
      ((Class.cab (nb077AlphaDummy149 x)
          (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
              (synCphi (Class.cv (nb077AlphaDummy150 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_155`. -/
@[expose]
noncomputable def nb077AlphaDummy155 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy148 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_156`. -/
@[expose]
noncomputable def nb077AlphaDummy156 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy148 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_157`. -/
@[expose]
noncomputable def nb077AlphaDummy157 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy150 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_158`. -/
@[expose]
noncomputable def nb077AlphaDummy158 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy150 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_159`. -/
@[expose]
noncomputable def nb077AlphaDummy159 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy155 F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy155 F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy155 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_160`. -/
@[expose]
noncomputable def nb077AlphaDummy160 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy157 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy157 x)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy157 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_161`. -/
@[expose]
noncomputable def nb077AlphaDummy161 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_162`. -/
@[expose]
noncomputable def nb077AlphaDummy162 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_163`. -/
@[expose]
noncomputable def nb077AlphaDummy163 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_164`. -/
@[expose]
noncomputable def nb077AlphaDummy164 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_165`. -/
@[expose]
noncomputable def nb077AlphaDummy165 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_166`. -/
@[expose]
noncomputable def nb077AlphaDummy166 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_167`. -/
@[expose]
noncomputable def nb077AlphaDummy167 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy162 F I))
          (Class.cv (nb077AlphaDummy163 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy162 F I))
          (Class.cv (nb077AlphaDummy163 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_168`. -/
@[expose]
noncomputable def nb077AlphaDummy168 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy165 x))
          (Class.cv (nb077AlphaDummy166 x)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy165 x)) (Class.cv (nb077AlphaDummy166 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_169`. -/
@[expose]
noncomputable def nb077AlphaDummy169 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy163 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_170`. -/
@[expose]
noncomputable def nb077AlphaDummy170 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy165 x))).fv ∪
      ((Class.cv (nb077AlphaDummy166 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_171`. -/
@[expose]
noncomputable def nb077AlphaDummy171 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy162 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy163 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_172`. -/
@[expose]
noncomputable def nb077AlphaDummy172 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy165 x)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy166 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_173`. -/
@[expose]
noncomputable def nb077AlphaDummy173 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy162 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_174`. -/
@[expose]
noncomputable def nb077AlphaDummy174 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy165 x))).fv ∪
      ((Class.cv (nb077AlphaDummy165 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_175`. -/
@[expose]
noncomputable def nb077AlphaDummy175 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy163 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy163 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_176`. -/
@[expose]
noncomputable def nb077AlphaDummy176 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy166 x))).fv ∪
      ((Class.cv (nb077AlphaDummy166 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_177`. -/
@[expose]
noncomputable def nb077AlphaDummy177 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy147 F I)
          (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy147 F I)
          (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_178`. -/
@[expose]
noncomputable def nb077AlphaDummy178 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy149 x)
          (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy149 x)
          (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_179`. -/
@[expose]
noncomputable def nb077AlphaDummy179 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy148 F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_180`. -/
@[expose]
noncomputable def nb077AlphaDummy180 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy150 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_181`. -/
@[expose]
noncomputable def nb077AlphaDummy181 (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy148 F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy148 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_182`. -/
@[expose]
noncomputable def nb077AlphaDummy182 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy150 x)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy150 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_183`. -/
@[expose]
noncomputable def nb077AlphaDummy183 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy141 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_184`. -/
@[expose]
noncomputable def nb077AlphaDummy184 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy141 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_185`. -/
@[expose]
noncomputable def nb077AlphaDummy185 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy142 x))).fv ∪
      ((Class.cv (nb077AlphaDummy144 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_186`. -/
@[expose]
noncomputable def nb077AlphaDummy186 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy142 x))).fv ∪
      ((Class.cv (nb077AlphaDummy144 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_187`. -/
@[expose]
noncomputable def nb077AlphaDummy187 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCphi (Class.cv (nb077AlphaDummy184 F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_188`. -/
@[expose]
noncomputable def nb077AlphaDummy188 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCphi (Class.cv (nb077AlphaDummy186 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_189`. -/
@[expose]
noncomputable def nb077AlphaDummy189 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy183 F I)
          (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
              (synCphi (Class.cv (nb077AlphaDummy184 F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy183 F I)
          (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
              (synCphi (Class.cv (nb077AlphaDummy184 F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_190`. -/
@[expose]
noncomputable def nb077AlphaDummy190 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy185 x)
          (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
              (synCphi (Class.cv (nb077AlphaDummy186 x))))))).fv ∪
      ((Class.cab (nb077AlphaDummy185 x)
          (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
              (synCphi (Class.cv (nb077AlphaDummy186 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_191`. -/
@[expose]
noncomputable def nb077AlphaDummy191 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy184 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_192`. -/
@[expose]
noncomputable def nb077AlphaDummy192 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy184 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_193`. -/
@[expose]
noncomputable def nb077AlphaDummy193 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy186 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_194`. -/
@[expose]
noncomputable def nb077AlphaDummy194 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy186 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_195`. -/
@[expose]
noncomputable def nb077AlphaDummy195 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy191 F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy191 F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy191 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_196`. -/
@[expose]
noncomputable def nb077AlphaDummy196 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy193 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy193 x)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy193 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_197`. -/
@[expose]
noncomputable def nb077AlphaDummy197 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_198`. -/
@[expose]
noncomputable def nb077AlphaDummy198 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_199`. -/
@[expose]
noncomputable def nb077AlphaDummy199 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_200`. -/
@[expose]
noncomputable def nb077AlphaDummy200 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_201`. -/
@[expose]
noncomputable def nb077AlphaDummy201 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_202`. -/
@[expose]
noncomputable def nb077AlphaDummy202 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_203`. -/
@[expose]
noncomputable def nb077AlphaDummy203 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy198 F I))
          (Class.cv (nb077AlphaDummy199 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy198 F I))
          (Class.cv (nb077AlphaDummy199 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_204`. -/
@[expose]
noncomputable def nb077AlphaDummy204 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy201 x))
          (Class.cv (nb077AlphaDummy202 x)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy201 x)) (Class.cv (nb077AlphaDummy202 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_205`. -/
@[expose]
noncomputable def nb077AlphaDummy205 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy199 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_206`. -/
@[expose]
noncomputable def nb077AlphaDummy206 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy201 x))).fv ∪
      ((Class.cv (nb077AlphaDummy202 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_207`. -/
@[expose]
noncomputable def nb077AlphaDummy207 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy198 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy199 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_208`. -/
@[expose]
noncomputable def nb077AlphaDummy208 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy201 x)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy202 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_209`. -/
@[expose]
noncomputable def nb077AlphaDummy209 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy198 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_210`. -/
@[expose]
noncomputable def nb077AlphaDummy210 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy201 x))).fv ∪
      ((Class.cv (nb077AlphaDummy201 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_211`. -/
@[expose]
noncomputable def nb077AlphaDummy211 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy199 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy199 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_212`. -/
@[expose]
noncomputable def nb077AlphaDummy212 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy202 x))).fv ∪
      ((Class.cv (nb077AlphaDummy202 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_213`. -/
@[expose]
noncomputable def nb077AlphaDummy213 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy183 F I)
          (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy183 F I)
          (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_214`. -/
@[expose]
noncomputable def nb077AlphaDummy214 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy185 x)
          (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy185 x)
          (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_215`. -/
@[expose]
noncomputable def nb077AlphaDummy215 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy184 F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_216`. -/
@[expose]
noncomputable def nb077AlphaDummy216 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy186 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_217`. -/
@[expose]
noncomputable def nb077AlphaDummy217 (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy184 F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy184 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_218`. -/
@[expose]
noncomputable def nb077AlphaDummy218 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy186 x)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy186 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_219`. -/
@[expose]
noncomputable def nb077AlphaDummy219 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy140 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_220`. -/
@[expose]
noncomputable def nb077AlphaDummy220 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy140 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_221`. -/
@[expose]
noncomputable def nb077AlphaDummy221 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy144 x))).fv ∪
      ((Class.cv (nb077AlphaDummy143 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_222`. -/
@[expose]
noncomputable def nb077AlphaDummy222 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy144 x))).fv ∪
      ((Class.cv (nb077AlphaDummy143 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_223`. -/
@[expose]
noncomputable def nb077AlphaDummy223 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCphi (Class.cv (nb077AlphaDummy220 F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_224`. -/
@[expose]
noncomputable def nb077AlphaDummy224 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCphi (Class.cv (nb077AlphaDummy222 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_225`. -/
@[expose]
noncomputable def nb077AlphaDummy225 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy219 F I)
          (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
              (synCphi (Class.cv (nb077AlphaDummy220 F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy219 F I)
          (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
              (synCphi (Class.cv (nb077AlphaDummy220 F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_226`. -/
@[expose]
noncomputable def nb077AlphaDummy226 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy221 x)
          (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
              (synCphi (Class.cv (nb077AlphaDummy222 x))))))).fv ∪
      ((Class.cab (nb077AlphaDummy221 x)
          (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
              (synCphi (Class.cv (nb077AlphaDummy222 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_227`. -/
@[expose]
noncomputable def nb077AlphaDummy227 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy220 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_228`. -/
@[expose]
noncomputable def nb077AlphaDummy228 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy220 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_229`. -/
@[expose]
noncomputable def nb077AlphaDummy229 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy222 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_230`. -/
@[expose]
noncomputable def nb077AlphaDummy230 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy222 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_231`. -/
@[expose]
noncomputable def nb077AlphaDummy231 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy227 F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy227 F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy227 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_232`. -/
@[expose]
noncomputable def nb077AlphaDummy232 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy229 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy229 x)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy229 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_233`. -/
@[expose]
noncomputable def nb077AlphaDummy233 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_234`. -/
@[expose]
noncomputable def nb077AlphaDummy234 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_235`. -/
@[expose]
noncomputable def nb077AlphaDummy235 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_236`. -/
@[expose]
noncomputable def nb077AlphaDummy236 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_237`. -/
@[expose]
noncomputable def nb077AlphaDummy237 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_238`. -/
@[expose]
noncomputable def nb077AlphaDummy238 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_239`. -/
@[expose]
noncomputable def nb077AlphaDummy239 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy234 F I))
          (Class.cv (nb077AlphaDummy235 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy234 F I))
          (Class.cv (nb077AlphaDummy235 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_240`. -/
@[expose]
noncomputable def nb077AlphaDummy240 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy237 x))
          (Class.cv (nb077AlphaDummy238 x)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy237 x)) (Class.cv (nb077AlphaDummy238 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_241`. -/
@[expose]
noncomputable def nb077AlphaDummy241 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy235 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_242`. -/
@[expose]
noncomputable def nb077AlphaDummy242 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy237 x))).fv ∪
      ((Class.cv (nb077AlphaDummy238 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_243`. -/
@[expose]
noncomputable def nb077AlphaDummy243 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy234 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy235 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_244`. -/
@[expose]
noncomputable def nb077AlphaDummy244 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy237 x)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy238 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_245`. -/
@[expose]
noncomputable def nb077AlphaDummy245 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy234 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_246`. -/
@[expose]
noncomputable def nb077AlphaDummy246 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy237 x))).fv ∪
      ((Class.cv (nb077AlphaDummy237 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_247`. -/
@[expose]
noncomputable def nb077AlphaDummy247 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy235 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy235 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_248`. -/
@[expose]
noncomputable def nb077AlphaDummy248 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy238 x))).fv ∪
      ((Class.cv (nb077AlphaDummy238 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_249`. -/
@[expose]
noncomputable def nb077AlphaDummy249 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy219 F I)
          (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy219 F I)
          (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_250`. -/
@[expose]
noncomputable def nb077AlphaDummy250 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy221 x)
          (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy221 x)
          (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_251`. -/
@[expose]
noncomputable def nb077AlphaDummy251 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy220 F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_252`. -/
@[expose]
noncomputable def nb077AlphaDummy252 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy222 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_253`. -/
@[expose]
noncomputable def nb077AlphaDummy253 (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy220 F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy220 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_254`. -/
@[expose]
noncomputable def nb077AlphaDummy254 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy222 x)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy222 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_255`. -/
@[expose]
noncomputable def nb077AlphaDummy255 (F : Class) (I : Class) : Var :=
  (freshVar (({(nb077AlphaDummy000 F I)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_256`. -/
@[expose]
noncomputable def nb077AlphaDummy256 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCplc (Class.cv x) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_257`. -/
@[expose]
noncomputable def nb077AlphaDummy257 (F : Class) (I : Class) : Var :=
  (freshVar (({(nb077AlphaDummy000 F I)} : Finset Var) ∪
        ({(nb077AlphaDummy255 F I)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb077AlphaDummy000 F I)) (synCvv))
          (Wff.classEq (Class.cv (nb077AlphaDummy255 F I))
            (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_258`. -/
@[expose]
noncomputable def nb077AlphaDummy258 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb077AlphaDummy256 x)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv x) (synCvv))
          (Wff.classEq (Class.cv (nb077AlphaDummy256 x))
            (synCplc (Class.cv x) (synC1c))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_259`. -/
@[expose]
noncomputable def nb077AlphaDummy259 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy255 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_260`. -/
@[expose]
noncomputable def nb077AlphaDummy260 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy255 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_261`. -/
@[expose]
noncomputable def nb077AlphaDummy261 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_262`. -/
@[expose]
noncomputable def nb077AlphaDummy262 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_263`. -/
@[expose]
noncomputable def nb077AlphaDummy263 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCphi (Class.cv (nb077AlphaDummy260 F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_264`. -/
@[expose]
noncomputable def nb077AlphaDummy264 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy261 x)
            (synWrex (nb077AlphaDummy262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCphi (Class.cv (nb077AlphaDummy262 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy261 x)
            (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_265`. -/
@[expose]
noncomputable def nb077AlphaDummy265 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy259 F I)
          (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
              (synCphi (Class.cv (nb077AlphaDummy260 F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy259 F I)
          (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
              (synCphi (Class.cv (nb077AlphaDummy260 F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_266`. -/
@[expose]
noncomputable def nb077AlphaDummy266 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy261 x)
          (synWrex (nb077AlphaDummy262 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
              (synCphi (Class.cv (nb077AlphaDummy262 x))))))).fv ∪
      ((Class.cab (nb077AlphaDummy261 x) (synWrex (nb077AlphaDummy262 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
              (synCphi (Class.cv (nb077AlphaDummy262 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_267`. -/
@[expose]
noncomputable def nb077AlphaDummy267 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy260 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_268`. -/
@[expose]
noncomputable def nb077AlphaDummy268 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy260 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_269`. -/
@[expose]
noncomputable def nb077AlphaDummy269 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy262 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_270`. -/
@[expose]
noncomputable def nb077AlphaDummy270 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy262 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_271`. -/
@[expose]
noncomputable def nb077AlphaDummy271 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy267 F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy267 F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy267 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_272`. -/
@[expose]
noncomputable def nb077AlphaDummy272 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy269 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy269 x)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy269 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_273`. -/
@[expose]
noncomputable def nb077AlphaDummy273 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_274`. -/
@[expose]
noncomputable def nb077AlphaDummy274 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_275`. -/
@[expose]
noncomputable def nb077AlphaDummy275 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_276`. -/
@[expose]
noncomputable def nb077AlphaDummy276 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_277`. -/
@[expose]
noncomputable def nb077AlphaDummy277 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_278`. -/
@[expose]
noncomputable def nb077AlphaDummy278 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_279`. -/
@[expose]
noncomputable def nb077AlphaDummy279 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy274 F I))
          (Class.cv (nb077AlphaDummy275 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy274 F I))
          (Class.cv (nb077AlphaDummy275 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_280`. -/
@[expose]
noncomputable def nb077AlphaDummy280 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy277 x))
          (Class.cv (nb077AlphaDummy278 x)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy277 x)) (Class.cv (nb077AlphaDummy278 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_281`. -/
@[expose]
noncomputable def nb077AlphaDummy281 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy275 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_282`. -/
@[expose]
noncomputable def nb077AlphaDummy282 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy277 x))).fv ∪
      ((Class.cv (nb077AlphaDummy278 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_283`. -/
@[expose]
noncomputable def nb077AlphaDummy283 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy274 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy275 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_284`. -/
@[expose]
noncomputable def nb077AlphaDummy284 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy277 x)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy278 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_285`. -/
@[expose]
noncomputable def nb077AlphaDummy285 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy274 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_286`. -/
@[expose]
noncomputable def nb077AlphaDummy286 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy277 x))).fv ∪
      ((Class.cv (nb077AlphaDummy277 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_287`. -/
@[expose]
noncomputable def nb077AlphaDummy287 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy275 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy275 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_288`. -/
@[expose]
noncomputable def nb077AlphaDummy288 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy278 x))).fv ∪
      ((Class.cv (nb077AlphaDummy278 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_289`. -/
@[expose]
noncomputable def nb077AlphaDummy289 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy259 F I)
          (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy259 F I)
          (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_290`. -/
@[expose]
noncomputable def nb077AlphaDummy290 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy261 x)
          (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy261 x)
          (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_291`. -/
@[expose]
noncomputable def nb077AlphaDummy291 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy260 F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_292`. -/
@[expose]
noncomputable def nb077AlphaDummy292 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy262 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_293`. -/
@[expose]
noncomputable def nb077AlphaDummy293 (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy260 F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy260 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_294`. -/
@[expose]
noncomputable def nb077AlphaDummy294 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy262 x)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy262 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_295`. -/
@[expose]
noncomputable def nb077AlphaDummy295 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_296`. -/
@[expose]
noncomputable def nb077AlphaDummy296 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_297`. -/
@[expose]
noncomputable def nb077AlphaDummy297 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_298`. -/
@[expose]
noncomputable def nb077AlphaDummy298 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_299`. -/
@[expose]
noncomputable def nb077AlphaDummy299 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((synC1c)).fv) 1)

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

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_300`. -/
@[expose]
noncomputable def nb077AlphaDummy300 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_301`. -/
@[expose]
noncomputable def nb077AlphaDummy301 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy296 F I))
          (Class.cv (nb077AlphaDummy297 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy296 F I))
          (Class.cv (nb077AlphaDummy297 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_302`. -/
@[expose]
noncomputable def nb077AlphaDummy302 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy299 x))
          (Class.cv (nb077AlphaDummy300 x)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy299 x)) (Class.cv (nb077AlphaDummy300 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_303`. -/
@[expose]
noncomputable def nb077AlphaDummy303 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy297 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_304`. -/
@[expose]
noncomputable def nb077AlphaDummy304 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy299 x))).fv ∪
      ((Class.cv (nb077AlphaDummy300 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_305`. -/
@[expose]
noncomputable def nb077AlphaDummy305 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy296 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy297 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_306`. -/
@[expose]
noncomputable def nb077AlphaDummy306 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy299 x)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy300 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_307`. -/
@[expose]
noncomputable def nb077AlphaDummy307 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy296 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_308`. -/
@[expose]
noncomputable def nb077AlphaDummy308 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy299 x))).fv ∪
      ((Class.cv (nb077AlphaDummy299 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_309`. -/
@[expose]
noncomputable def nb077AlphaDummy309 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy297 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy297 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_310`. -/
@[expose]
noncomputable def nb077AlphaDummy310 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy300 x))).fv ∪
      ((Class.cv (nb077AlphaDummy300 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_311`. -/
@[expose]
noncomputable def nb077AlphaDummy311 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy060 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_312`. -/
@[expose]
noncomputable def nb077AlphaDummy312 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy060 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_313`. -/
@[expose]
noncomputable def nb077AlphaDummy313 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy064 x))).fv ∪
      ((Class.cv (nb077AlphaDummy063 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_314`. -/
@[expose]
noncomputable def nb077AlphaDummy314 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy064 x))).fv ∪
      ((Class.cv (nb077AlphaDummy063 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_315`. -/
@[expose]
noncomputable def nb077AlphaDummy315 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCphi (Class.cv (nb077AlphaDummy312 F I)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_316`. -/
@[expose]
noncomputable def nb077AlphaDummy316 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCphi (Class.cv (nb077AlphaDummy314 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_317`. -/
@[expose]
noncomputable def nb077AlphaDummy317 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy311 F I)
          (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
              (synCphi (Class.cv (nb077AlphaDummy312 F I))))))).fv ∪
      ((Class.cab (nb077AlphaDummy311 F I)
          (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
              (synCphi (Class.cv (nb077AlphaDummy312 F I))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_318`. -/
@[expose]
noncomputable def nb077AlphaDummy318 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy313 x)
          (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
              (synCphi (Class.cv (nb077AlphaDummy314 x))))))).fv ∪
      ((Class.cab (nb077AlphaDummy313 x)
          (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
              (synCphi (Class.cv (nb077AlphaDummy314 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_319`. -/
@[expose]
noncomputable def nb077AlphaDummy319 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy312 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_320`. -/
@[expose]
noncomputable def nb077AlphaDummy320 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy312 F I))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_321`. -/
@[expose]
noncomputable def nb077AlphaDummy321 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy314 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_322`. -/
@[expose]
noncomputable def nb077AlphaDummy322 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy314 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_323`. -/
@[expose]
noncomputable def nb077AlphaDummy323 (F : Class) (I : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy319 F I)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy319 F I)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy319 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_324`. -/
@[expose]
noncomputable def nb077AlphaDummy324 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb077AlphaDummy321 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb077AlphaDummy321 x)) (synC1c))).fv ∪
      ((Class.cv (nb077AlphaDummy321 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_325`. -/
@[expose]
noncomputable def nb077AlphaDummy325 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_326`. -/
@[expose]
noncomputable def nb077AlphaDummy326 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_327`. -/
@[expose]
noncomputable def nb077AlphaDummy327 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_328`. -/
@[expose]
noncomputable def nb077AlphaDummy328 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_329`. -/
@[expose]
noncomputable def nb077AlphaDummy329 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_330`. -/
@[expose]
noncomputable def nb077AlphaDummy330 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_331`. -/
@[expose]
noncomputable def nb077AlphaDummy331 (F : Class) (I : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy326 F I))
          (Class.cv (nb077AlphaDummy327 F I)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy326 F I))
          (Class.cv (nb077AlphaDummy327 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_332`. -/
@[expose]
noncomputable def nb077AlphaDummy332 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb077AlphaDummy329 x))
          (Class.cv (nb077AlphaDummy330 x)))).fv ∪
      ((synCnin (Class.cv (nb077AlphaDummy329 x)) (Class.cv (nb077AlphaDummy330 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_333`. -/
@[expose]
noncomputable def nb077AlphaDummy333 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy327 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_334`. -/
@[expose]
noncomputable def nb077AlphaDummy334 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy329 x))).fv ∪
      ((Class.cv (nb077AlphaDummy330 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_335`. -/
@[expose]
noncomputable def nb077AlphaDummy335 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy326 F I)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy327 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_336`. -/
@[expose]
noncomputable def nb077AlphaDummy336 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb077AlphaDummy329 x)))).fv ∪
      ((synCcompl (Class.cv (nb077AlphaDummy330 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_337`. -/
@[expose]
noncomputable def nb077AlphaDummy337 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy326 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_338`. -/
@[expose]
noncomputable def nb077AlphaDummy338 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy329 x))).fv ∪
      ((Class.cv (nb077AlphaDummy329 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_339`. -/
@[expose]
noncomputable def nb077AlphaDummy339 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy327 F I))).fv ∪
      ((Class.cv (nb077AlphaDummy327 F I))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_340`. -/
@[expose]
noncomputable def nb077AlphaDummy340 (x : Var) : Var :=
  (freshVar (((Class.cv (nb077AlphaDummy330 x))).fv ∪
      ((Class.cv (nb077AlphaDummy330 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_341`. -/
@[expose]
noncomputable def nb077AlphaDummy341 (F : Class) (I : Class) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy311 F I)
          (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy311 F I)
          (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
            (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
              (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_342`. -/
@[expose]
noncomputable def nb077AlphaDummy342 (x : Var) : Var :=
  (freshVar (((Class.cab (nb077AlphaDummy313 x)
          (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy313 x)
          (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
            (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
              (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_343`. -/
@[expose]
noncomputable def nb077AlphaDummy343 (F : Class) (I : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy312 F I))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_344`. -/
@[expose]
noncomputable def nb077AlphaDummy344 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb077AlphaDummy314 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_345`. -/
@[expose]
noncomputable def nb077AlphaDummy345 (F : Class) (I : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy312 F I)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy312 F I)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb077_alpha_dummy_346`. -/
@[expose]
noncomputable def nb077AlphaDummy346 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb077AlphaDummy314 x)))).fv ∪
      ((synCphi (Class.cv (nb077AlphaDummy314 x)))).fv) 0)

theorem nb077_fresh_000 (F : Class) (I : Class) :
    (nb077AlphaDummy003 F I) ∉
      (((Class.cab (nb077AlphaDummy001 F I) (synWa (synWss (synCsn (synCop (synC0c) I))
              (Class.cv (nb077AlphaDummy001 F I))) (synWss (synCima (synCpprod
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                (Class.cv (nb077AlphaDummy001 F I)))
              (Class.cv (nb077AlphaDummy001 F I)))))).fv) :=
  by
  simpa only [nb077AlphaDummy003] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy001 F I) (synWa (synWss (synCsn (synCop (synC0c) I))
              (Class.cv (nb077AlphaDummy001 F I))) (synWss (synCima (synCpprod
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                (Class.cv (nb077AlphaDummy001 F I)))
              (Class.cv (nb077AlphaDummy001 F I)))))).fv)
      0

theorem nb077_fresh_001 (F : Class) (I : Class) :
    (nb077AlphaDummy004 F I) ∉
      (((Class.cab (nb077AlphaDummy001 F I) (synWa (synWss (synCsn (synCop (synC0c) I))
              (Class.cv (nb077AlphaDummy001 F I))) (synWss (synCima (synCpprod
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                (Class.cv (nb077AlphaDummy001 F I)))
              (Class.cv (nb077AlphaDummy001 F I)))))).fv) :=
  by
  simpa only [nb077AlphaDummy004] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy001 F I) (synWa (synWss (synCsn (synCop (synC0c) I))
              (Class.cv (nb077AlphaDummy001 F I))) (synWss (synCima (synCpprod
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                (Class.cv (nb077AlphaDummy001 F I)))
              (Class.cv (nb077AlphaDummy001 F I)))))).fv)
      1

theorem nb077_distinct_002 (F : Class) (I : Class) :
    (nb077AlphaDummy003 F I) ≠ (nb077AlphaDummy004 F I) := by
  simpa only [nb077AlphaDummy003, nb077AlphaDummy004] using
    (freshVar_injective (((Class.cab (nb077AlphaDummy001 F I) (synWa
            (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy001 F I)))
            (synWss (synCima (synCpprod (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                (Class.cv (nb077AlphaDummy001 F I)))
              (Class.cv (nb077AlphaDummy001 F I)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_003 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy005 x F I) ∉
      (((Class.cab (nb077AlphaDummy002 x F I) (synWa
            (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
            (synWss (synCima
                (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                (Class.cv (nb077AlphaDummy002 x F I)))
              (Class.cv (nb077AlphaDummy002 x F I)))))).fv) :=
  by
  simpa only [nb077AlphaDummy005] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy002 x F I) (synWa
            (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
            (synWss (synCima
                (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                (Class.cv (nb077AlphaDummy002 x F I)))
              (Class.cv (nb077AlphaDummy002 x F I)))))).fv)
      0

theorem nb077_fresh_004 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy006 x F I) ∉
      (((Class.cab (nb077AlphaDummy002 x F I) (synWa
            (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
            (synWss (synCima
                (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                (Class.cv (nb077AlphaDummy002 x F I)))
              (Class.cv (nb077AlphaDummy002 x F I)))))).fv) :=
  by
  simpa only [nb077AlphaDummy006] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy002 x F I) (synWa
            (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
            (synWss (synCima
                (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                (Class.cv (nb077AlphaDummy002 x F I)))
              (Class.cv (nb077AlphaDummy002 x F I)))))).fv)
      1

theorem nb077_distinct_005 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy005 x F I) ≠ (nb077AlphaDummy006 x F I) := by
  simpa only [nb077AlphaDummy005, nb077AlphaDummy006] using
    (freshVar_injective (((Class.cab (nb077AlphaDummy002 x F I) (synWa
            (synWss (synCsn (synCop (synC0c) I)) (Class.cv (nb077AlphaDummy002 x F I)))
            (synWss (synCima
                (synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                (Class.cv (nb077AlphaDummy002 x F I)))
              (Class.cv (nb077AlphaDummy002 x F I)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_006 (F : Class) (I : Class) :
    (nb077AlphaDummy049 F I) ∉
      (((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_007 (F : Class) (I : Class) :
    (nb077AlphaDummy025 F I) ∉
      (((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCphi (Class.cv (nb077AlphaDummy020 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCphi (Class.cv (nb077AlphaDummy020 F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy025] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCphi (Class.cv (nb077AlphaDummy020 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCphi (Class.cv (nb077AlphaDummy020 F I))))))).fv)
      0

theorem nb077_fresh_008 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy050 x F I) ∉
      (((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy017 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy021 x F I)
            (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy017 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy050] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy017 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy021 x F I)
            (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy017 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_009 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy026 x F I) ∉
      (((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy018 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy018 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy026] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy018 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy018 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))).fv)
      0

theorem nb077_fresh_010 (F : Class) (I : Class) :
    (nb077AlphaDummy073 F I) ∉
      (((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCphi (Class.cv (nb077AlphaDummy068 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCphi (Class.cv (nb077AlphaDummy068 F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCphi (Class.cv (nb077AlphaDummy068 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCphi (Class.cv (nb077AlphaDummy068 F I))))))).fv)
      0

theorem nb077_fresh_011 (F : Class) (I : Class) :
    (nb077AlphaDummy097 F I) ∉
      (((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy097] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_012 (x : Var) :
    (nb077AlphaDummy074 x) ∉
      (((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCphi (Class.cv (nb077AlphaDummy070 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCphi (Class.cv (nb077AlphaDummy070 x))))))).fv) :=
  by
  simpa only [nb077AlphaDummy074] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCphi (Class.cv (nb077AlphaDummy070 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCphi (Class.cv (nb077AlphaDummy070 x))))))).fv)
      0

theorem nb077_fresh_013 (x : Var) :
    (nb077AlphaDummy098 x) ∉
      (((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy098] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_014 (F : Class) (I : Class) :
    (nb077AlphaDummy109 F I) ∉
      (((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCphi (Class.cv (nb077AlphaDummy104 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCphi (Class.cv (nb077AlphaDummy104 F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy109] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCphi (Class.cv (nb077AlphaDummy104 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCphi (Class.cv (nb077AlphaDummy104 F I))))))).fv)
      0

theorem nb077_fresh_015 (F : Class) (I : Class) :
    (nb077AlphaDummy133 F I) ∉
      (((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy133] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_016 (x : Var) :
    (nb077AlphaDummy110 x) ∉
      (((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCphi (Class.cv (nb077AlphaDummy106 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCphi (Class.cv (nb077AlphaDummy106 x))))))).fv) :=
  by
  simpa only [nb077AlphaDummy110] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCphi (Class.cv (nb077AlphaDummy106 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCphi (Class.cv (nb077AlphaDummy106 x))))))).fv)
      0

theorem nb077_fresh_017 (x : Var) :
    (nb077AlphaDummy134 x) ∉
      (((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy134] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_018 (F : Class) (I : Class) :
    (nb077AlphaDummy153 F I) ∉
      (((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCphi (Class.cv (nb077AlphaDummy148 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCphi (Class.cv (nb077AlphaDummy148 F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy153] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCphi (Class.cv (nb077AlphaDummy148 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCphi (Class.cv (nb077AlphaDummy148 F I))))))).fv)
      0

theorem nb077_fresh_019 (F : Class) (I : Class) :
    (nb077AlphaDummy177 F I) ∉
      (((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy177] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_020 (x : Var) :
    (nb077AlphaDummy154 x) ∉
      (((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCphi (Class.cv (nb077AlphaDummy150 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCphi (Class.cv (nb077AlphaDummy150 x))))))).fv) :=
  by
  simpa only [nb077AlphaDummy154] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCphi (Class.cv (nb077AlphaDummy150 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCphi (Class.cv (nb077AlphaDummy150 x))))))).fv)
      0

theorem nb077_fresh_021 (x : Var) :
    (nb077AlphaDummy178 x) ∉
      (((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy178] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_022 (F : Class) (I : Class) :
    (nb077AlphaDummy189 F I) ∉
      (((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCphi (Class.cv (nb077AlphaDummy184 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCphi (Class.cv (nb077AlphaDummy184 F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy189] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCphi (Class.cv (nb077AlphaDummy184 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCphi (Class.cv (nb077AlphaDummy184 F I))))))).fv)
      0

theorem nb077_fresh_023 (F : Class) (I : Class) :
    (nb077AlphaDummy213 F I) ∉
      (((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy213] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy183 F I)
            (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_024 (x : Var) :
    (nb077AlphaDummy190 x) ∉
      (((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCphi (Class.cv (nb077AlphaDummy186 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCphi (Class.cv (nb077AlphaDummy186 x))))))).fv) :=
  by
  simpa only [nb077AlphaDummy190] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCphi (Class.cv (nb077AlphaDummy186 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCphi (Class.cv (nb077AlphaDummy186 x))))))).fv)
      0

theorem nb077_fresh_025 (x : Var) :
    (nb077AlphaDummy214 x) ∉
      (((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy214] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy185 x)
            (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_026 (F : Class) (I : Class) :
    (nb077AlphaDummy249 F I) ∉
      (((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy249] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_027 (F : Class) (I : Class) :
    (nb077AlphaDummy225 F I) ∉
      (((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCphi (Class.cv (nb077AlphaDummy220 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCphi (Class.cv (nb077AlphaDummy220 F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy225] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCphi (Class.cv (nb077AlphaDummy220 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy219 F I)
            (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                (synCphi (Class.cv (nb077AlphaDummy220 F I))))))).fv)
      0

theorem nb077_fresh_028 (x : Var) :
    (nb077AlphaDummy250 x) ∉
      (((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy250] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_029 (x : Var) :
    (nb077AlphaDummy226 x) ∉
      (((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCphi (Class.cv (nb077AlphaDummy222 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCphi (Class.cv (nb077AlphaDummy222 x))))))).fv) :=
  by
  simpa only [nb077AlphaDummy226] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCphi (Class.cv (nb077AlphaDummy222 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy221 x)
            (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                (synCphi (Class.cv (nb077AlphaDummy222 x))))))).fv)
      0

theorem nb077_fresh_030 (F : Class) (I : Class) :
    (nb077AlphaDummy265 F I) ∉
      (((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCphi (Class.cv (nb077AlphaDummy260 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCphi (Class.cv (nb077AlphaDummy260 F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy265] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCphi (Class.cv (nb077AlphaDummy260 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCphi (Class.cv (nb077AlphaDummy260 F I))))))).fv)
      0

theorem nb077_fresh_031 (F : Class) (I : Class) :
    (nb077AlphaDummy289 F I) ∉
      (((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy289] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy259 F I)
            (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_032 (x : Var) :
    (nb077AlphaDummy290 x) ∉
      (((Class.cab (nb077AlphaDummy261 x)
            (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy261 x)
            (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy290] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy261 x)
            (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy261 x)
            (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_033 (x : Var) :
    (nb077AlphaDummy266 x) ∉
      (((Class.cab (nb077AlphaDummy261 x) (synWrex (nb077AlphaDummy262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCphi (Class.cv (nb077AlphaDummy262 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy261 x) (synWrex (nb077AlphaDummy262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCphi (Class.cv (nb077AlphaDummy262 x))))))).fv) :=
  by
  simpa only [nb077AlphaDummy266] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy261 x) (synWrex (nb077AlphaDummy262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCphi (Class.cv (nb077AlphaDummy262 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy261 x) (synWrex (nb077AlphaDummy262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                (synCphi (Class.cv (nb077AlphaDummy262 x))))))).fv)
      0

theorem nb077_fresh_034 (F : Class) (I : Class) :
    (nb077AlphaDummy341 F I) ∉
      (((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy341] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_035 (F : Class) (I : Class) :
    (nb077AlphaDummy317 F I) ∉
      (((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCphi (Class.cv (nb077AlphaDummy312 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCphi (Class.cv (nb077AlphaDummy312 F I))))))).fv) :=
  by
  simpa only [nb077AlphaDummy317] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCphi (Class.cv (nb077AlphaDummy312 F I))))))).fv ∪
        ((Class.cab (nb077AlphaDummy311 F I)
            (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                (synCphi (Class.cv (nb077AlphaDummy312 F I))))))).fv)
      0

theorem nb077_fresh_036 (x : Var) :
    (nb077AlphaDummy342 x) ∉
      (((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb077AlphaDummy342] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb077_fresh_037 (x : Var) :
    (nb077AlphaDummy318 x) ∉
      (((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCphi (Class.cv (nb077AlphaDummy314 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCphi (Class.cv (nb077AlphaDummy314 x))))))).fv) :=
  by
  simpa only [nb077AlphaDummy318] using
    freshVar_not_mem
      (((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCphi (Class.cv (nb077AlphaDummy314 x))))))).fv ∪
        ((Class.cab (nb077AlphaDummy313 x)
            (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                (synCphi (Class.cv (nb077AlphaDummy314 x))))))).fv)
      0

theorem nb077_fresh_038 (F : Class) (I : Class) :
    (nb077AlphaDummy259 F I) ∉
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy259] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv)
      0

theorem nb077_fresh_039 (F : Class) (I : Class) :
    (nb077AlphaDummy260 F I) ∉
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy260] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv)
      1

theorem nb077_distinct_040 (F : Class) (I : Class) :
    (nb077AlphaDummy259 F I) ≠ (nb077AlphaDummy260 F I) := by
  simpa only [nb077AlphaDummy259, nb077AlphaDummy260] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy000 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy255 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_041 (F : Class) (I : Class) :
    (nb077AlphaDummy295 F I) ∉
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy295] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_042 (F : Class) (I : Class) :
    (nb077AlphaDummy296 F I) ∉
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy296] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_043 (F : Class) (I : Class) :
    (nb077AlphaDummy297 F I) ∉
      (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy297] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_044 (F : Class) (I : Class) :
    (nb077AlphaDummy295 F I) ≠ (nb077AlphaDummy296 F I) := by
  simpa only [nb077AlphaDummy295, nb077AlphaDummy296] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_045 (F : Class) (I : Class) :
    (nb077AlphaDummy295 F I) ≠ (nb077AlphaDummy297 F I) := by
  simpa only [nb077AlphaDummy295, nb077AlphaDummy297] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_046 (F : Class) (I : Class) :
    (nb077AlphaDummy296 F I) ≠ (nb077AlphaDummy297 F I) := by
  simpa only [nb077AlphaDummy296, nb077AlphaDummy297] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy000 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_047 (F : Class) (I : Class) :
    (nb077AlphaDummy019 F I) ∉
      (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy019] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv)
      0

theorem nb077_fresh_048 (F : Class) (I : Class) :
    (nb077AlphaDummy020 F I) ∉
      (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy020] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv)
      1

theorem nb077_distinct_049 (F : Class) (I : Class) :
    (nb077AlphaDummy019 F I) ≠ (nb077AlphaDummy020 F I) := by
  simpa only [nb077AlphaDummy019, nb077AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_050 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy021 x F I) ∉
      (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy017 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy021] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy017 x F I))).fv)
      0

theorem nb077_fresh_051 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy022 x F I) ∉
      (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy017 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy022] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy017 x F I))).fv)
      1

theorem nb077_distinct_052 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy021 x F I) ≠ (nb077AlphaDummy022 x F I) := by
  simpa only [nb077AlphaDummy021, nb077AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy017 x F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_053 (F : Class) (I : Class) :
    (nb077AlphaDummy027 F I) ∉ (((Class.cv (nb077AlphaDummy020 F I))).fv) := by
  simpa only [nb077AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy020 F I))).fv) 0

theorem nb077_fresh_054 (F : Class) (I : Class) :
    (nb077AlphaDummy028 F I) ∉ (((Class.cv (nb077AlphaDummy020 F I))).fv) := by
  simpa only [nb077AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy020 F I))).fv) 1

theorem nb077_distinct_055 (F : Class) (I : Class) :
    (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy028 F I) := by
  simpa only [nb077AlphaDummy027, nb077AlphaDummy028] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy020 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_056 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy029 x F I) ∉ (((Class.cv (nb077AlphaDummy022 x F I))).fv) := by
  simpa only [nb077AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy022 x F I))).fv) 0

theorem nb077_fresh_057 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy030 x F I) ∉ (((Class.cv (nb077AlphaDummy022 x F I))).fv) := by
  simpa only [nb077AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy022 x F I))).fv) 1

theorem nb077_distinct_058 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy030 x F I) := by
  simpa only [nb077AlphaDummy029, nb077AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy022 x F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_059 (F : Class) (I : Class) :
    (nb077AlphaDummy033 F I) ∉
      (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_060 (F : Class) (I : Class) :
    (nb077AlphaDummy034 F I) ∉
      (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy034] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_061 (F : Class) (I : Class) :
    (nb077AlphaDummy035 F I) ∉
      (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy035] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_062 (F : Class) (I : Class) :
    (nb077AlphaDummy033 F I) ≠ (nb077AlphaDummy034 F I) := by
  simpa only [nb077AlphaDummy033, nb077AlphaDummy034] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_063 (F : Class) (I : Class) :
    (nb077AlphaDummy033 F I) ≠ (nb077AlphaDummy035 F I) := by
  simpa only [nb077AlphaDummy033, nb077AlphaDummy035] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_064 (F : Class) (I : Class) :
    (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy035 F I) := by
  simpa only [nb077AlphaDummy034, nb077AlphaDummy035] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_065 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy036 x F I) ∉
      (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy036] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_066 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy037 x F I) ∉
      (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy037] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_067 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy038 x F I) ∉
      (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy038] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_068 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy036 x F I) ≠ (nb077AlphaDummy037 x F I) := by
  simpa only [nb077AlphaDummy036, nb077AlphaDummy037] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv)
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
    (nb077AlphaDummy036 x F I) ≠ (nb077AlphaDummy038 x F I) := by
  simpa only [nb077AlphaDummy036, nb077AlphaDummy038] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_070 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy038 x F I) := by
  simpa only [nb077AlphaDummy037, nb077AlphaDummy038] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_071 (F : Class) (I : Class) :
    (nb077AlphaDummy045 F I) ∉
      (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy034 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy034 F I))).fv)
      0

theorem nb077_fresh_072 (F : Class) (I : Class) :
    (nb077AlphaDummy041 F I) ∉
      (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy035 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy034 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy035 F I))).fv)
      0

theorem nb077_fresh_073 (F : Class) (I : Class) :
    (nb077AlphaDummy047 F I) ∉
      (((Class.cv (nb077AlphaDummy035 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy035 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy047] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy035 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy035 F I))).fv)
      0

theorem nb077_fresh_074 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy046 x F I) ∉
      (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy037 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy037 x F I))).fv)
      0

theorem nb077_fresh_075 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy042 x F I) ∉
      (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy038 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy037 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy038 x F I))).fv)
      0

theorem nb077_fresh_076 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy048 x F I) ∉
      (((Class.cv (nb077AlphaDummy038 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy038 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy048] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy038 x F I))).fv ∪
        ((Class.cv (nb077AlphaDummy038 x F I))).fv)
      0

theorem nb077_fresh_077 (F : Class) (I : Class) :
    (nb077AlphaDummy067 F I) ∉
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv)
      0

theorem nb077_fresh_078 (F : Class) (I : Class) :
    (nb077AlphaDummy068 F I) ∉
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv)
      1

theorem nb077_distinct_079 (F : Class) (I : Class) :
    (nb077AlphaDummy067 F I) ≠ (nb077AlphaDummy068 F I) := by
  simpa only [nb077AlphaDummy067, nb077AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_080 (F : Class) (I : Class) :
    (nb077AlphaDummy103 F I) ∉
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy103] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv)
      0

theorem nb077_fresh_081 (F : Class) (I : Class) :
    (nb077AlphaDummy104 F I) ∉
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy104] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv)
      1

theorem nb077_distinct_082 (F : Class) (I : Class) :
    (nb077AlphaDummy103 F I) ≠ (nb077AlphaDummy104 F I) := by
  simpa only [nb077AlphaDummy103, nb077AlphaDummy104] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_083 (F : Class) (I : Class) :
    (nb077AlphaDummy311 F I) ∉
      (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy311] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv)
      0

theorem nb077_fresh_084 (F : Class) (I : Class) :
    (nb077AlphaDummy312 F I) ∉
      (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy312] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv)
      1

theorem nb077_distinct_085 (F : Class) (I : Class) :
    (nb077AlphaDummy311 F I) ≠ (nb077AlphaDummy312 F I) := by
  simpa only [nb077AlphaDummy311, nb077AlphaDummy312] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy061 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_086 (x : Var) :
    (nb077AlphaDummy069 x) ∉
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv) :=
  by
  simpa only [nb077AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv)
      0

theorem nb077_fresh_087 (x : Var) :
    (nb077AlphaDummy070 x) ∉
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv) :=
  by
  simpa only [nb077AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv)
      1

theorem nb077_distinct_088 (x : Var) :
    (nb077AlphaDummy069 x) ≠ (nb077AlphaDummy070 x) := by
  simpa only [nb077AlphaDummy069, nb077AlphaDummy070] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy062 x))).fv ∪
        ((Class.cv (nb077AlphaDummy063 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_089 (x : Var) :
    (nb077AlphaDummy105 x) ∉
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv) :=
  by
  simpa only [nb077AlphaDummy105] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv)
      0

theorem nb077_fresh_090 (x : Var) :
    (nb077AlphaDummy106 x) ∉
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv) :=
  by
  simpa only [nb077AlphaDummy106] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv)
      1

theorem nb077_distinct_091 (x : Var) :
    (nb077AlphaDummy105 x) ≠ (nb077AlphaDummy106 x) := by
  simpa only [nb077AlphaDummy105, nb077AlphaDummy106] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy062 x))).fv ∪
        ((Class.cv (nb077AlphaDummy064 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_092 (x : Var) :
    (nb077AlphaDummy313 x) ∉
      (((Class.cv (nb077AlphaDummy064 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv) :=
  by
  simpa only [nb077AlphaDummy313] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy064 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv)
      0

theorem nb077_fresh_093 (x : Var) :
    (nb077AlphaDummy314 x) ∉
      (((Class.cv (nb077AlphaDummy064 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv) :=
  by
  simpa only [nb077AlphaDummy314] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy064 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv)
      1

theorem nb077_distinct_094 (x : Var) :
    (nb077AlphaDummy313 x) ≠ (nb077AlphaDummy314 x) := by
  simpa only [nb077AlphaDummy313, nb077AlphaDummy314] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy064 x))).fv ∪
        ((Class.cv (nb077AlphaDummy063 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_095 (F : Class) (I : Class) :
    (nb077AlphaDummy075 F I) ∉ (((Class.cv (nb077AlphaDummy068 F I))).fv) := by
  simpa only [nb077AlphaDummy075] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy068 F I))).fv) 0

theorem nb077_fresh_096 (F : Class) (I : Class) :
    (nb077AlphaDummy076 F I) ∉ (((Class.cv (nb077AlphaDummy068 F I))).fv) := by
  simpa only [nb077AlphaDummy076] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy068 F I))).fv) 1

theorem nb077_distinct_097 (F : Class) (I : Class) :
    (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy076 F I) := by
  simpa only [nb077AlphaDummy075, nb077AlphaDummy076] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy068 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_098 (x : Var) :
    (nb077AlphaDummy077 x) ∉ (((Class.cv (nb077AlphaDummy070 x))).fv) := by
  simpa only [nb077AlphaDummy077] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy070 x))).fv) 0

theorem nb077_fresh_099 (x : Var) :
    (nb077AlphaDummy078 x) ∉ (((Class.cv (nb077AlphaDummy070 x))).fv) := by
  simpa only [nb077AlphaDummy078] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy070 x))).fv) 1

theorem nb077_distinct_100 (x : Var) :
    (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy078 x) := by
  simpa only [nb077AlphaDummy077, nb077AlphaDummy078] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy070 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_101 (F : Class) (I : Class) :
    (nb077AlphaDummy081 F I) ∉
      (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy081] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_102 (F : Class) (I : Class) :
    (nb077AlphaDummy082 F I) ∉
      (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy082] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_103 (F : Class) (I : Class) :
    (nb077AlphaDummy083 F I) ∉
      (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy083] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_104 (F : Class) (I : Class) :
    (nb077AlphaDummy081 F I) ≠ (nb077AlphaDummy082 F I) := by
  simpa only [nb077AlphaDummy081, nb077AlphaDummy082] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_105 (F : Class) (I : Class) :
    (nb077AlphaDummy081 F I) ≠ (nb077AlphaDummy083 F I) := by
  simpa only [nb077AlphaDummy081, nb077AlphaDummy083] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_106 (F : Class) (I : Class) :
    (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy083 F I) := by
  simpa only [nb077AlphaDummy082, nb077AlphaDummy083] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_107 (x : Var) :
    (nb077AlphaDummy084 x) ∉
      (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy084] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_108 (x : Var) :
    (nb077AlphaDummy085 x) ∉
      (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy085] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_109 (x : Var) :
    (nb077AlphaDummy086 x) ∉
      (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy086] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_110 (x : Var) :
    (nb077AlphaDummy084 x) ≠ (nb077AlphaDummy085 x) := by
  simpa only [nb077AlphaDummy084, nb077AlphaDummy085] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_111 (x : Var) :
    (nb077AlphaDummy084 x) ≠ (nb077AlphaDummy086 x) := by
  simpa only [nb077AlphaDummy084, nb077AlphaDummy086] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_112 (x : Var) :
    (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy086 x) := by
  simpa only [nb077AlphaDummy085, nb077AlphaDummy086] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_113 (F : Class) (I : Class) :
    (nb077AlphaDummy093 F I) ∉
      (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy082 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy093] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy082 F I))).fv)
      0

theorem nb077_fresh_114 (F : Class) (I : Class) :
    (nb077AlphaDummy089 F I) ∉
      (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy083 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy089] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy082 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy083 F I))).fv)
      0

theorem nb077_fresh_115 (F : Class) (I : Class) :
    (nb077AlphaDummy095 F I) ∉
      (((Class.cv (nb077AlphaDummy083 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy083 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy095] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy083 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy083 F I))).fv)
      0

theorem nb077_fresh_116 (x : Var) :
    (nb077AlphaDummy094 x) ∉
      (((Class.cv (nb077AlphaDummy085 x))).fv ∪ ((Class.cv (nb077AlphaDummy085 x))).fv) :=
  by
  simpa only [nb077AlphaDummy094] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy085 x))).fv ∪ ((Class.cv (nb077AlphaDummy085 x))).fv)
      0

theorem nb077_fresh_117 (x : Var) :
    (nb077AlphaDummy090 x) ∉
      (((Class.cv (nb077AlphaDummy085 x))).fv ∪ ((Class.cv (nb077AlphaDummy086 x))).fv) :=
  by
  simpa only [nb077AlphaDummy090] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy085 x))).fv ∪ ((Class.cv (nb077AlphaDummy086 x))).fv)
      0

theorem nb077_fresh_118 (x : Var) :
    (nb077AlphaDummy096 x) ∉
      (((Class.cv (nb077AlphaDummy086 x))).fv ∪ ((Class.cv (nb077AlphaDummy086 x))).fv) :=
  by
  simpa only [nb077AlphaDummy096] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy086 x))).fv ∪ ((Class.cv (nb077AlphaDummy086 x))).fv)
      0

theorem nb077_fresh_119 (F : Class) (I : Class) :
    (nb077AlphaDummy111 F I) ∉ (((Class.cv (nb077AlphaDummy104 F I))).fv) := by
  simpa only [nb077AlphaDummy111] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy104 F I))).fv) 0

theorem nb077_fresh_120 (F : Class) (I : Class) :
    (nb077AlphaDummy112 F I) ∉ (((Class.cv (nb077AlphaDummy104 F I))).fv) := by
  simpa only [nb077AlphaDummy112] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy104 F I))).fv) 1

theorem nb077_distinct_121 (F : Class) (I : Class) :
    (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy112 F I) := by
  simpa only [nb077AlphaDummy111, nb077AlphaDummy112] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy104 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_122 (x : Var) :
    (nb077AlphaDummy113 x) ∉ (((Class.cv (nb077AlphaDummy106 x))).fv) := by
  simpa only [nb077AlphaDummy113] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy106 x))).fv) 0

theorem nb077_fresh_123 (x : Var) :
    (nb077AlphaDummy114 x) ∉ (((Class.cv (nb077AlphaDummy106 x))).fv) := by
  simpa only [nb077AlphaDummy114] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy106 x))).fv) 1

theorem nb077_distinct_124 (x : Var) :
    (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy114 x) := by
  simpa only [nb077AlphaDummy113, nb077AlphaDummy114] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy106 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_125 (F : Class) (I : Class) :
    (nb077AlphaDummy117 F I) ∉
      (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy117] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_126 (F : Class) (I : Class) :
    (nb077AlphaDummy118 F I) ∉
      (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy118] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_127 (F : Class) (I : Class) :
    (nb077AlphaDummy119 F I) ∉
      (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy119] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_128 (F : Class) (I : Class) :
    (nb077AlphaDummy117 F I) ≠ (nb077AlphaDummy118 F I) := by
  simpa only [nb077AlphaDummy117, nb077AlphaDummy118] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_129 (F : Class) (I : Class) :
    (nb077AlphaDummy117 F I) ≠ (nb077AlphaDummy119 F I) := by
  simpa only [nb077AlphaDummy117, nb077AlphaDummy119] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_130 (F : Class) (I : Class) :
    (nb077AlphaDummy118 F I) ≠ (nb077AlphaDummy119 F I) := by
  simpa only [nb077AlphaDummy118, nb077AlphaDummy119] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_131 (x : Var) :
    (nb077AlphaDummy120 x) ∉
      (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy120] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_132 (x : Var) :
    (nb077AlphaDummy121 x) ∉
      (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy121] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_133 (x : Var) :
    (nb077AlphaDummy122 x) ∉
      (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy122] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_134 (x : Var) :
    (nb077AlphaDummy120 x) ≠ (nb077AlphaDummy121 x) := by
  simpa only [nb077AlphaDummy120, nb077AlphaDummy121] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_135 (x : Var) :
    (nb077AlphaDummy120 x) ≠ (nb077AlphaDummy122 x) := by
  simpa only [nb077AlphaDummy120, nb077AlphaDummy122] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_136 (x : Var) :
    (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy122 x) := by
  simpa only [nb077AlphaDummy121, nb077AlphaDummy122] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_137 (F : Class) (I : Class) :
    (nb077AlphaDummy129 F I) ∉
      (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy118 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy129] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy118 F I))).fv)
      0

theorem nb077_fresh_138 (F : Class) (I : Class) :
    (nb077AlphaDummy125 F I) ∉
      (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy119 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy125] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy118 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy119 F I))).fv)
      0

theorem nb077_fresh_139 (F : Class) (I : Class) :
    (nb077AlphaDummy131 F I) ∉
      (((Class.cv (nb077AlphaDummy119 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy119 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy131] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy119 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy119 F I))).fv)
      0

theorem nb077_fresh_140 (x : Var) :
    (nb077AlphaDummy130 x) ∉
      (((Class.cv (nb077AlphaDummy121 x))).fv ∪ ((Class.cv (nb077AlphaDummy121 x))).fv) :=
  by
  simpa only [nb077AlphaDummy130] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy121 x))).fv ∪ ((Class.cv (nb077AlphaDummy121 x))).fv)
      0

theorem nb077_fresh_141 (x : Var) :
    (nb077AlphaDummy126 x) ∉
      (((Class.cv (nb077AlphaDummy121 x))).fv ∪ ((Class.cv (nb077AlphaDummy122 x))).fv) :=
  by
  simpa only [nb077AlphaDummy126] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy121 x))).fv ∪ ((Class.cv (nb077AlphaDummy122 x))).fv)
      0

theorem nb077_fresh_142 (x : Var) :
    (nb077AlphaDummy132 x) ∉
      (((Class.cv (nb077AlphaDummy122 x))).fv ∪ ((Class.cv (nb077AlphaDummy122 x))).fv) :=
  by
  simpa only [nb077AlphaDummy132] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy122 x))).fv ∪ ((Class.cv (nb077AlphaDummy122 x))).fv)
      0

theorem nb077_fresh_143 (F : Class) (I : Class) :
    (nb077AlphaDummy147 F I) ∉
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy147] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv)
      0

theorem nb077_fresh_144 (F : Class) (I : Class) :
    (nb077AlphaDummy148 F I) ∉
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy148] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv)
      1

theorem nb077_distinct_145 (F : Class) (I : Class) :
    (nb077AlphaDummy147 F I) ≠ (nb077AlphaDummy148 F I) := by
  simpa only [nb077AlphaDummy147, nb077AlphaDummy148] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_146 (F : Class) (I : Class) :
    (nb077AlphaDummy183 F I) ∉
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy141 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy183] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy141 F I))).fv)
      0

theorem nb077_fresh_147 (F : Class) (I : Class) :
    (nb077AlphaDummy184 F I) ∉
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy141 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy184] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy141 F I))).fv)
      1

theorem nb077_distinct_148 (F : Class) (I : Class) :
    (nb077AlphaDummy183 F I) ≠ (nb077AlphaDummy184 F I) := by
  simpa only [nb077AlphaDummy183, nb077AlphaDummy184] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy141 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_149 (F : Class) (I : Class) :
    (nb077AlphaDummy219 F I) ∉
      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy219] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv)
      0

theorem nb077_fresh_150 (F : Class) (I : Class) :
    (nb077AlphaDummy220 F I) ∉
      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy220] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv)
      1

theorem nb077_distinct_151 (F : Class) (I : Class) :
    (nb077AlphaDummy219 F I) ≠ (nb077AlphaDummy220 F I) := by
  simpa only [nb077AlphaDummy219, nb077AlphaDummy220] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy141 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_152 (x : Var) :
    (nb077AlphaDummy149 x) ∉
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv) :=
  by
  simpa only [nb077AlphaDummy149] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv)
      0

theorem nb077_fresh_153 (x : Var) :
    (nb077AlphaDummy150 x) ∉
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv) :=
  by
  simpa only [nb077AlphaDummy150] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv)
      1

theorem nb077_distinct_154 (x : Var) :
    (nb077AlphaDummy149 x) ≠ (nb077AlphaDummy150 x) := by
  simpa only [nb077AlphaDummy149, nb077AlphaDummy150] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy142 x))).fv ∪
        ((Class.cv (nb077AlphaDummy143 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_155 (x : Var) :
    (nb077AlphaDummy185 x) ∉
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy144 x))).fv) :=
  by
  simpa only [nb077AlphaDummy185] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy144 x))).fv)
      0

theorem nb077_fresh_156 (x : Var) :
    (nb077AlphaDummy186 x) ∉
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy144 x))).fv) :=
  by
  simpa only [nb077AlphaDummy186] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy144 x))).fv)
      1

theorem nb077_distinct_157 (x : Var) :
    (nb077AlphaDummy185 x) ≠ (nb077AlphaDummy186 x) := by
  simpa only [nb077AlphaDummy185, nb077AlphaDummy186] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy142 x))).fv ∪
        ((Class.cv (nb077AlphaDummy144 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_158 (x : Var) :
    (nb077AlphaDummy221 x) ∉
      (((Class.cv (nb077AlphaDummy144 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv) :=
  by
  simpa only [nb077AlphaDummy221] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy144 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv)
      0

theorem nb077_fresh_159 (x : Var) :
    (nb077AlphaDummy222 x) ∉
      (((Class.cv (nb077AlphaDummy144 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv) :=
  by
  simpa only [nb077AlphaDummy222] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy144 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv)
      1

theorem nb077_distinct_160 (x : Var) :
    (nb077AlphaDummy221 x) ≠ (nb077AlphaDummy222 x) := by
  simpa only [nb077AlphaDummy221, nb077AlphaDummy222] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy144 x))).fv ∪
        ((Class.cv (nb077AlphaDummy143 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_161 (F : Class) (I : Class) :
    (nb077AlphaDummy155 F I) ∉ (((Class.cv (nb077AlphaDummy148 F I))).fv) := by
  simpa only [nb077AlphaDummy155] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy148 F I))).fv) 0

theorem nb077_fresh_162 (F : Class) (I : Class) :
    (nb077AlphaDummy156 F I) ∉ (((Class.cv (nb077AlphaDummy148 F I))).fv) := by
  simpa only [nb077AlphaDummy156] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy148 F I))).fv) 1

theorem nb077_distinct_163 (F : Class) (I : Class) :
    (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy156 F I) := by
  simpa only [nb077AlphaDummy155, nb077AlphaDummy156] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy148 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_164 (x : Var) :
    (nb077AlphaDummy157 x) ∉ (((Class.cv (nb077AlphaDummy150 x))).fv) := by
  simpa only [nb077AlphaDummy157] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy150 x))).fv) 0

theorem nb077_fresh_165 (x : Var) :
    (nb077AlphaDummy158 x) ∉ (((Class.cv (nb077AlphaDummy150 x))).fv) := by
  simpa only [nb077AlphaDummy158] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy150 x))).fv) 1

theorem nb077_distinct_166 (x : Var) :
    (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy158 x) := by
  simpa only [nb077AlphaDummy157, nb077AlphaDummy158] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy150 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_167 (F : Class) (I : Class) :
    (nb077AlphaDummy161 F I) ∉
      (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy161] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_168 (F : Class) (I : Class) :
    (nb077AlphaDummy162 F I) ∉
      (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy162] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_169 (F : Class) (I : Class) :
    (nb077AlphaDummy163 F I) ∉
      (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy163] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_170 (F : Class) (I : Class) :
    (nb077AlphaDummy161 F I) ≠ (nb077AlphaDummy162 F I) := by
  simpa only [nb077AlphaDummy161, nb077AlphaDummy162] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_171 (F : Class) (I : Class) :
    (nb077AlphaDummy161 F I) ≠ (nb077AlphaDummy163 F I) := by
  simpa only [nb077AlphaDummy161, nb077AlphaDummy163] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_172 (F : Class) (I : Class) :
    (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy163 F I) := by
  simpa only [nb077AlphaDummy162, nb077AlphaDummy163] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_173 (x : Var) :
    (nb077AlphaDummy164 x) ∉
      (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy164] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_174 (x : Var) :
    (nb077AlphaDummy165 x) ∉
      (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy165] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_175 (x : Var) :
    (nb077AlphaDummy166 x) ∉
      (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy166] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_176 (x : Var) :
    (nb077AlphaDummy164 x) ≠ (nb077AlphaDummy165 x) := by
  simpa only [nb077AlphaDummy164, nb077AlphaDummy165] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_177 (x : Var) :
    (nb077AlphaDummy164 x) ≠ (nb077AlphaDummy166 x) := by
  simpa only [nb077AlphaDummy164, nb077AlphaDummy166] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_178 (x : Var) :
    (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy166 x) := by
  simpa only [nb077AlphaDummy165, nb077AlphaDummy166] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_179 (F : Class) (I : Class) :
    (nb077AlphaDummy173 F I) ∉
      (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy162 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy173] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy162 F I))).fv)
      0

theorem nb077_fresh_180 (F : Class) (I : Class) :
    (nb077AlphaDummy169 F I) ∉
      (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy163 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy169] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy162 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy163 F I))).fv)
      0

theorem nb077_fresh_181 (F : Class) (I : Class) :
    (nb077AlphaDummy175 F I) ∉
      (((Class.cv (nb077AlphaDummy163 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy163 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy175] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy163 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy163 F I))).fv)
      0

theorem nb077_fresh_182 (x : Var) :
    (nb077AlphaDummy174 x) ∉
      (((Class.cv (nb077AlphaDummy165 x))).fv ∪ ((Class.cv (nb077AlphaDummy165 x))).fv) :=
  by
  simpa only [nb077AlphaDummy174] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy165 x))).fv ∪ ((Class.cv (nb077AlphaDummy165 x))).fv)
      0

theorem nb077_fresh_183 (x : Var) :
    (nb077AlphaDummy170 x) ∉
      (((Class.cv (nb077AlphaDummy165 x))).fv ∪ ((Class.cv (nb077AlphaDummy166 x))).fv) :=
  by
  simpa only [nb077AlphaDummy170] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy165 x))).fv ∪ ((Class.cv (nb077AlphaDummy166 x))).fv)
      0

theorem nb077_fresh_184 (x : Var) :
    (nb077AlphaDummy176 x) ∉
      (((Class.cv (nb077AlphaDummy166 x))).fv ∪ ((Class.cv (nb077AlphaDummy166 x))).fv) :=
  by
  simpa only [nb077AlphaDummy176] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy166 x))).fv ∪ ((Class.cv (nb077AlphaDummy166 x))).fv)
      0

theorem nb077_fresh_185 (F : Class) (I : Class) :
    (nb077AlphaDummy191 F I) ∉ (((Class.cv (nb077AlphaDummy184 F I))).fv) := by
  simpa only [nb077AlphaDummy191] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy184 F I))).fv) 0

theorem nb077_fresh_186 (F : Class) (I : Class) :
    (nb077AlphaDummy192 F I) ∉ (((Class.cv (nb077AlphaDummy184 F I))).fv) := by
  simpa only [nb077AlphaDummy192] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy184 F I))).fv) 1

theorem nb077_distinct_187 (F : Class) (I : Class) :
    (nb077AlphaDummy191 F I) ≠ (nb077AlphaDummy192 F I) := by
  simpa only [nb077AlphaDummy191, nb077AlphaDummy192] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy184 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_188 (x : Var) :
    (nb077AlphaDummy193 x) ∉ (((Class.cv (nb077AlphaDummy186 x))).fv) := by
  simpa only [nb077AlphaDummy193] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy186 x))).fv) 0

theorem nb077_fresh_189 (x : Var) :
    (nb077AlphaDummy194 x) ∉ (((Class.cv (nb077AlphaDummy186 x))).fv) := by
  simpa only [nb077AlphaDummy194] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy186 x))).fv) 1

theorem nb077_distinct_190 (x : Var) :
    (nb077AlphaDummy193 x) ≠ (nb077AlphaDummy194 x) := by
  simpa only [nb077AlphaDummy193, nb077AlphaDummy194] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy186 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_191 (F : Class) (I : Class) :
    (nb077AlphaDummy197 F I) ∉
      (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy197] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_192 (F : Class) (I : Class) :
    (nb077AlphaDummy198 F I) ∉
      (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy198] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_193 (F : Class) (I : Class) :
    (nb077AlphaDummy199 F I) ∉
      (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy199] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_194 (F : Class) (I : Class) :
    (nb077AlphaDummy197 F I) ≠ (nb077AlphaDummy198 F I) := by
  simpa only [nb077AlphaDummy197, nb077AlphaDummy198] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_195 (F : Class) (I : Class) :
    (nb077AlphaDummy197 F I) ≠ (nb077AlphaDummy199 F I) := by
  simpa only [nb077AlphaDummy197, nb077AlphaDummy199] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_196 (F : Class) (I : Class) :
    (nb077AlphaDummy198 F I) ≠ (nb077AlphaDummy199 F I) := by
  simpa only [nb077AlphaDummy198, nb077AlphaDummy199] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy191 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_197 (x : Var) :
    (nb077AlphaDummy200 x) ∉
      (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy200] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_198 (x : Var) :
    (nb077AlphaDummy201 x) ∉
      (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy201] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_199 (x : Var) :
    (nb077AlphaDummy202 x) ∉
      (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy202] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_200 (x : Var) :
    (nb077AlphaDummy200 x) ≠ (nb077AlphaDummy201 x) := by
  simpa only [nb077AlphaDummy200, nb077AlphaDummy201] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_201 (x : Var) :
    (nb077AlphaDummy200 x) ≠ (nb077AlphaDummy202 x) := by
  simpa only [nb077AlphaDummy200, nb077AlphaDummy202] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_202 (x : Var) :
    (nb077AlphaDummy201 x) ≠ (nb077AlphaDummy202 x) := by
  simpa only [nb077AlphaDummy201, nb077AlphaDummy202] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy193 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_203 (F : Class) (I : Class) :
    (nb077AlphaDummy209 F I) ∉
      (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy198 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy209] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy198 F I))).fv)
      0

theorem nb077_fresh_204 (F : Class) (I : Class) :
    (nb077AlphaDummy205 F I) ∉
      (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy199 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy205] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy198 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy199 F I))).fv)
      0

theorem nb077_fresh_205 (F : Class) (I : Class) :
    (nb077AlphaDummy211 F I) ∉
      (((Class.cv (nb077AlphaDummy199 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy199 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy211] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy199 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy199 F I))).fv)
      0

theorem nb077_fresh_206 (x : Var) :
    (nb077AlphaDummy210 x) ∉
      (((Class.cv (nb077AlphaDummy201 x))).fv ∪ ((Class.cv (nb077AlphaDummy201 x))).fv) :=
  by
  simpa only [nb077AlphaDummy210] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy201 x))).fv ∪ ((Class.cv (nb077AlphaDummy201 x))).fv)
      0

theorem nb077_fresh_207 (x : Var) :
    (nb077AlphaDummy206 x) ∉
      (((Class.cv (nb077AlphaDummy201 x))).fv ∪ ((Class.cv (nb077AlphaDummy202 x))).fv) :=
  by
  simpa only [nb077AlphaDummy206] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy201 x))).fv ∪ ((Class.cv (nb077AlphaDummy202 x))).fv)
      0

theorem nb077_fresh_208 (x : Var) :
    (nb077AlphaDummy212 x) ∉
      (((Class.cv (nb077AlphaDummy202 x))).fv ∪ ((Class.cv (nb077AlphaDummy202 x))).fv) :=
  by
  simpa only [nb077AlphaDummy212] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy202 x))).fv ∪ ((Class.cv (nb077AlphaDummy202 x))).fv)
      0

theorem nb077_fresh_209 (F : Class) (I : Class) :
    (nb077AlphaDummy227 F I) ∉ (((Class.cv (nb077AlphaDummy220 F I))).fv) := by
  simpa only [nb077AlphaDummy227] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy220 F I))).fv) 0

theorem nb077_fresh_210 (F : Class) (I : Class) :
    (nb077AlphaDummy228 F I) ∉ (((Class.cv (nb077AlphaDummy220 F I))).fv) := by
  simpa only [nb077AlphaDummy228] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy220 F I))).fv) 1

theorem nb077_distinct_211 (F : Class) (I : Class) :
    (nb077AlphaDummy227 F I) ≠ (nb077AlphaDummy228 F I) := by
  simpa only [nb077AlphaDummy227, nb077AlphaDummy228] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy220 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_212 (x : Var) :
    (nb077AlphaDummy229 x) ∉ (((Class.cv (nb077AlphaDummy222 x))).fv) := by
  simpa only [nb077AlphaDummy229] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy222 x))).fv) 0

theorem nb077_fresh_213 (x : Var) :
    (nb077AlphaDummy230 x) ∉ (((Class.cv (nb077AlphaDummy222 x))).fv) := by
  simpa only [nb077AlphaDummy230] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy222 x))).fv) 1

theorem nb077_distinct_214 (x : Var) :
    (nb077AlphaDummy229 x) ≠ (nb077AlphaDummy230 x) := by
  simpa only [nb077AlphaDummy229, nb077AlphaDummy230] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy222 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_215 (F : Class) (I : Class) :
    (nb077AlphaDummy233 F I) ∉
      (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy233] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_216 (F : Class) (I : Class) :
    (nb077AlphaDummy234 F I) ∉
      (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy234] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_217 (F : Class) (I : Class) :
    (nb077AlphaDummy235 F I) ∉
      (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy235] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_218 (F : Class) (I : Class) :
    (nb077AlphaDummy233 F I) ≠ (nb077AlphaDummy234 F I) := by
  simpa only [nb077AlphaDummy233, nb077AlphaDummy234] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv)
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
    (nb077AlphaDummy233 F I) ≠ (nb077AlphaDummy235 F I) := by
  simpa only [nb077AlphaDummy233, nb077AlphaDummy235] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_220 (F : Class) (I : Class) :
    (nb077AlphaDummy234 F I) ≠ (nb077AlphaDummy235 F I) := by
  simpa only [nb077AlphaDummy234, nb077AlphaDummy235] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy227 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_221 (x : Var) :
    (nb077AlphaDummy236 x) ∉
      (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy236] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_222 (x : Var) :
    (nb077AlphaDummy237 x) ∉
      (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy237] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_223 (x : Var) :
    (nb077AlphaDummy238 x) ∉
      (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy238] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_224 (x : Var) :
    (nb077AlphaDummy236 x) ≠ (nb077AlphaDummy237 x) := by
  simpa only [nb077AlphaDummy236, nb077AlphaDummy237] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_225 (x : Var) :
    (nb077AlphaDummy236 x) ≠ (nb077AlphaDummy238 x) := by
  simpa only [nb077AlphaDummy236, nb077AlphaDummy238] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_226 (x : Var) :
    (nb077AlphaDummy237 x) ≠ (nb077AlphaDummy238 x) := by
  simpa only [nb077AlphaDummy237, nb077AlphaDummy238] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy229 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_227 (F : Class) (I : Class) :
    (nb077AlphaDummy245 F I) ∉
      (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy234 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy245] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy234 F I))).fv)
      0

theorem nb077_fresh_228 (F : Class) (I : Class) :
    (nb077AlphaDummy241 F I) ∉
      (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy235 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy241] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy234 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy235 F I))).fv)
      0

theorem nb077_fresh_229 (F : Class) (I : Class) :
    (nb077AlphaDummy247 F I) ∉
      (((Class.cv (nb077AlphaDummy235 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy235 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy247] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy235 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy235 F I))).fv)
      0

theorem nb077_fresh_230 (x : Var) :
    (nb077AlphaDummy246 x) ∉
      (((Class.cv (nb077AlphaDummy237 x))).fv ∪ ((Class.cv (nb077AlphaDummy237 x))).fv) :=
  by
  simpa only [nb077AlphaDummy246] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy237 x))).fv ∪ ((Class.cv (nb077AlphaDummy237 x))).fv)
      0

theorem nb077_fresh_231 (x : Var) :
    (nb077AlphaDummy242 x) ∉
      (((Class.cv (nb077AlphaDummy237 x))).fv ∪ ((Class.cv (nb077AlphaDummy238 x))).fv) :=
  by
  simpa only [nb077AlphaDummy242] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy237 x))).fv ∪ ((Class.cv (nb077AlphaDummy238 x))).fv)
      0

theorem nb077_fresh_232 (x : Var) :
    (nb077AlphaDummy248 x) ∉
      (((Class.cv (nb077AlphaDummy238 x))).fv ∪ ((Class.cv (nb077AlphaDummy238 x))).fv) :=
  by
  simpa only [nb077AlphaDummy248] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy238 x))).fv ∪ ((Class.cv (nb077AlphaDummy238 x))).fv)
      0

theorem nb077_fresh_233 (F : Class) (I : Class) :
    (nb077AlphaDummy267 F I) ∉ (((Class.cv (nb077AlphaDummy260 F I))).fv) := by
  simpa only [nb077AlphaDummy267] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy260 F I))).fv) 0

theorem nb077_fresh_234 (F : Class) (I : Class) :
    (nb077AlphaDummy268 F I) ∉ (((Class.cv (nb077AlphaDummy260 F I))).fv) := by
  simpa only [nb077AlphaDummy268] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy260 F I))).fv) 1

theorem nb077_distinct_235 (F : Class) (I : Class) :
    (nb077AlphaDummy267 F I) ≠ (nb077AlphaDummy268 F I) := by
  simpa only [nb077AlphaDummy267, nb077AlphaDummy268] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy260 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_236 (x : Var) :
    (nb077AlphaDummy269 x) ∉ (((Class.cv (nb077AlphaDummy262 x))).fv) := by
  simpa only [nb077AlphaDummy269] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy262 x))).fv) 0

theorem nb077_fresh_237 (x : Var) :
    (nb077AlphaDummy270 x) ∉ (((Class.cv (nb077AlphaDummy262 x))).fv) := by
  simpa only [nb077AlphaDummy270] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy262 x))).fv) 1

theorem nb077_distinct_238 (x : Var) :
    (nb077AlphaDummy269 x) ≠ (nb077AlphaDummy270 x) := by
  simpa only [nb077AlphaDummy269, nb077AlphaDummy270] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy262 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_239 (F : Class) (I : Class) :
    (nb077AlphaDummy273 F I) ∉
      (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy273] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_240 (F : Class) (I : Class) :
    (nb077AlphaDummy274 F I) ∉
      (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy274] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_241 (F : Class) (I : Class) :
    (nb077AlphaDummy275 F I) ∉
      (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy275] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_242 (F : Class) (I : Class) :
    (nb077AlphaDummy273 F I) ≠ (nb077AlphaDummy274 F I) := by
  simpa only [nb077AlphaDummy273, nb077AlphaDummy274] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_243 (F : Class) (I : Class) :
    (nb077AlphaDummy273 F I) ≠ (nb077AlphaDummy275 F I) := by
  simpa only [nb077AlphaDummy273, nb077AlphaDummy275] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_244 (F : Class) (I : Class) :
    (nb077AlphaDummy274 F I) ≠ (nb077AlphaDummy275 F I) := by
  simpa only [nb077AlphaDummy274, nb077AlphaDummy275] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy267 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_245 (x : Var) :
    (nb077AlphaDummy276 x) ∉
      (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy276] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_246 (x : Var) :
    (nb077AlphaDummy277 x) ∉
      (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy277] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_247 (x : Var) :
    (nb077AlphaDummy278 x) ∉
      (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy278] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_248 (x : Var) :
    (nb077AlphaDummy276 x) ≠ (nb077AlphaDummy277 x) := by
  simpa only [nb077AlphaDummy276, nb077AlphaDummy277] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_249 (x : Var) :
    (nb077AlphaDummy276 x) ≠ (nb077AlphaDummy278 x) := by
  simpa only [nb077AlphaDummy276, nb077AlphaDummy278] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_250 (x : Var) :
    (nb077AlphaDummy277 x) ≠ (nb077AlphaDummy278 x) := by
  simpa only [nb077AlphaDummy277, nb077AlphaDummy278] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy269 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_251 (F : Class) (I : Class) :
    (nb077AlphaDummy285 F I) ∉
      (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy274 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy285] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy274 F I))).fv)
      0

theorem nb077_fresh_252 (F : Class) (I : Class) :
    (nb077AlphaDummy281 F I) ∉
      (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy275 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy281] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy274 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy275 F I))).fv)
      0

theorem nb077_fresh_253 (F : Class) (I : Class) :
    (nb077AlphaDummy287 F I) ∉
      (((Class.cv (nb077AlphaDummy275 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy275 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy287] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy275 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy275 F I))).fv)
      0

theorem nb077_fresh_254 (x : Var) :
    (nb077AlphaDummy286 x) ∉
      (((Class.cv (nb077AlphaDummy277 x))).fv ∪ ((Class.cv (nb077AlphaDummy277 x))).fv) :=
  by
  simpa only [nb077AlphaDummy286] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy277 x))).fv ∪ ((Class.cv (nb077AlphaDummy277 x))).fv)
      0

theorem nb077_fresh_255 (x : Var) :
    (nb077AlphaDummy282 x) ∉
      (((Class.cv (nb077AlphaDummy277 x))).fv ∪ ((Class.cv (nb077AlphaDummy278 x))).fv) :=
  by
  simpa only [nb077AlphaDummy282] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy277 x))).fv ∪ ((Class.cv (nb077AlphaDummy278 x))).fv)
      0

theorem nb077_fresh_256 (x : Var) :
    (nb077AlphaDummy288 x) ∉
      (((Class.cv (nb077AlphaDummy278 x))).fv ∪ ((Class.cv (nb077AlphaDummy278 x))).fv) :=
  by
  simpa only [nb077AlphaDummy288] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy278 x))).fv ∪ ((Class.cv (nb077AlphaDummy278 x))).fv)
      0

theorem nb077_fresh_257 (F : Class) (I : Class) :
    (nb077AlphaDummy307 F I) ∉
      (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy296 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy307] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy296 F I))).fv)
      0

theorem nb077_fresh_258 (F : Class) (I : Class) :
    (nb077AlphaDummy303 F I) ∉
      (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy297 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy303] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy296 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy297 F I))).fv)
      0

theorem nb077_fresh_259 (F : Class) (I : Class) :
    (nb077AlphaDummy309 F I) ∉
      (((Class.cv (nb077AlphaDummy297 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy297 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy309] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy297 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy297 F I))).fv)
      0

theorem nb077_fresh_260 (x : Var) :
    (nb077AlphaDummy308 x) ∉
      (((Class.cv (nb077AlphaDummy299 x))).fv ∪ ((Class.cv (nb077AlphaDummy299 x))).fv) :=
  by
  simpa only [nb077AlphaDummy308] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy299 x))).fv ∪ ((Class.cv (nb077AlphaDummy299 x))).fv)
      0

theorem nb077_fresh_261 (x : Var) :
    (nb077AlphaDummy304 x) ∉
      (((Class.cv (nb077AlphaDummy299 x))).fv ∪ ((Class.cv (nb077AlphaDummy300 x))).fv) :=
  by
  simpa only [nb077AlphaDummy304] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy299 x))).fv ∪ ((Class.cv (nb077AlphaDummy300 x))).fv)
      0

theorem nb077_fresh_262 (x : Var) :
    (nb077AlphaDummy310 x) ∉
      (((Class.cv (nb077AlphaDummy300 x))).fv ∪ ((Class.cv (nb077AlphaDummy300 x))).fv) :=
  by
  simpa only [nb077AlphaDummy310] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy300 x))).fv ∪ ((Class.cv (nb077AlphaDummy300 x))).fv)
      0

theorem nb077_fresh_263 (F : Class) (I : Class) :
    (nb077AlphaDummy319 F I) ∉ (((Class.cv (nb077AlphaDummy312 F I))).fv) := by
  simpa only [nb077AlphaDummy319] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy312 F I))).fv) 0

theorem nb077_fresh_264 (F : Class) (I : Class) :
    (nb077AlphaDummy320 F I) ∉ (((Class.cv (nb077AlphaDummy312 F I))).fv) := by
  simpa only [nb077AlphaDummy320] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy312 F I))).fv) 1

theorem nb077_distinct_265 (F : Class) (I : Class) :
    (nb077AlphaDummy319 F I) ≠ (nb077AlphaDummy320 F I) := by
  simpa only [nb077AlphaDummy319, nb077AlphaDummy320] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy312 F I))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_266 (x : Var) :
    (nb077AlphaDummy321 x) ∉ (((Class.cv (nb077AlphaDummy314 x))).fv) := by
  simpa only [nb077AlphaDummy321] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy314 x))).fv) 0

theorem nb077_fresh_267 (x : Var) :
    (nb077AlphaDummy322 x) ∉ (((Class.cv (nb077AlphaDummy314 x))).fv) := by
  simpa only [nb077AlphaDummy322] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy314 x))).fv) 1

theorem nb077_distinct_268 (x : Var) :
    (nb077AlphaDummy321 x) ≠ (nb077AlphaDummy322 x) := by
  simpa only [nb077AlphaDummy321, nb077AlphaDummy322] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy314 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb077_fresh_269 (F : Class) (I : Class) :
    (nb077AlphaDummy325 F I) ∉
      (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy325] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_270 (F : Class) (I : Class) :
    (nb077AlphaDummy326 F I) ∉
      (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy326] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_271 (F : Class) (I : Class) :
    (nb077AlphaDummy327 F I) ∉
      (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy327] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_272 (F : Class) (I : Class) :
    (nb077AlphaDummy325 F I) ≠ (nb077AlphaDummy326 F I) := by
  simpa only [nb077AlphaDummy325, nb077AlphaDummy326] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_273 (F : Class) (I : Class) :
    (nb077AlphaDummy325 F I) ≠ (nb077AlphaDummy327 F I) := by
  simpa only [nb077AlphaDummy325, nb077AlphaDummy327] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_274 (F : Class) (I : Class) :
    (nb077AlphaDummy326 F I) ≠ (nb077AlphaDummy327 F I) := by
  simpa only [nb077AlphaDummy326, nb077AlphaDummy327] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy319 F I))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_275 (x : Var) :
    (nb077AlphaDummy328 x) ∉
      (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy328] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_276 (x : Var) :
    (nb077AlphaDummy329 x) ∉
      (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy329] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_277 (x : Var) :
    (nb077AlphaDummy330 x) ∉
      (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb077AlphaDummy330] using
    freshVar_not_mem (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_278 (x : Var) :
    (nb077AlphaDummy328 x) ≠ (nb077AlphaDummy329 x) := by
  simpa only [nb077AlphaDummy328, nb077AlphaDummy329] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb077_distinct_279 (x : Var) :
    (nb077AlphaDummy328 x) ≠ (nb077AlphaDummy330 x) := by
  simpa only [nb077AlphaDummy328, nb077AlphaDummy330] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb077_distinct_280 (x : Var) :
    (nb077AlphaDummy329 x) ≠ (nb077AlphaDummy330 x) := by
  simpa only [nb077AlphaDummy329, nb077AlphaDummy330] using
    (freshVar_injective (((Class.cv (nb077AlphaDummy321 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb077_fresh_281 (F : Class) (I : Class) :
    (nb077AlphaDummy337 F I) ∉
      (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy326 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy337] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy326 F I))).fv)
      0

theorem nb077_fresh_282 (F : Class) (I : Class) :
    (nb077AlphaDummy333 F I) ∉
      (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy327 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy333] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy326 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy327 F I))).fv)
      0

theorem nb077_fresh_283 (F : Class) (I : Class) :
    (nb077AlphaDummy339 F I) ∉
      (((Class.cv (nb077AlphaDummy327 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy327 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy339] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy327 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy327 F I))).fv)
      0

theorem nb077_fresh_284 (x : Var) :
    (nb077AlphaDummy338 x) ∉
      (((Class.cv (nb077AlphaDummy329 x))).fv ∪ ((Class.cv (nb077AlphaDummy329 x))).fv) :=
  by
  simpa only [nb077AlphaDummy338] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy329 x))).fv ∪ ((Class.cv (nb077AlphaDummy329 x))).fv)
      0

theorem nb077_fresh_285 (x : Var) :
    (nb077AlphaDummy334 x) ∉
      (((Class.cv (nb077AlphaDummy329 x))).fv ∪ ((Class.cv (nb077AlphaDummy330 x))).fv) :=
  by
  simpa only [nb077AlphaDummy334] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy329 x))).fv ∪ ((Class.cv (nb077AlphaDummy330 x))).fv)
      0

theorem nb077_fresh_286 (x : Var) :
    (nb077AlphaDummy340 x) ∉
      (((Class.cv (nb077AlphaDummy330 x))).fv ∪ ((Class.cv (nb077AlphaDummy330 x))).fv) :=
  by
  simpa only [nb077AlphaDummy340] using
    freshVar_not_mem
      (((Class.cv (nb077AlphaDummy330 x))).fv ∪ ((Class.cv (nb077AlphaDummy330 x))).fv)
      0

theorem nb077_fresh_287 (x : Var) :
    (nb077AlphaDummy261 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) :=
  by
  simpa only [nb077AlphaDummy261] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) 0

theorem nb077_fresh_288 (x : Var) :
    (nb077AlphaDummy262 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) :=
  by
  simpa only [nb077AlphaDummy262] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv) 1

theorem nb077_distinct_289 (x : Var) :
    (nb077AlphaDummy261 x) ≠ (nb077AlphaDummy262 x) := by
  simpa only [nb077AlphaDummy261, nb077AlphaDummy262] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb077AlphaDummy256 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_fresh_290 (x : Var) :
    (nb077AlphaDummy298 x) ∉ (((Class.cv x)).fv ∪ ((synC1c)).fv) := by
  simpa only [nb077AlphaDummy298] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((synC1c)).fv) 0

theorem nb077_fresh_291 (x : Var) :
    (nb077AlphaDummy299 x) ∉ (((Class.cv x)).fv ∪ ((synC1c)).fv) := by
  simpa only [nb077AlphaDummy299] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((synC1c)).fv) 1

theorem nb077_fresh_292 (x : Var) :
    (nb077AlphaDummy300 x) ∉ (((Class.cv x)).fv ∪ ((synC1c)).fv) := by
  simpa only [nb077AlphaDummy300] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((synC1c)).fv) 2

theorem nb077_distinct_293 (x : Var) :
    (nb077AlphaDummy298 x) ≠ (nb077AlphaDummy299 x) := by
  simpa only [nb077AlphaDummy298, nb077AlphaDummy299] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_294 (x : Var) :
    (nb077AlphaDummy298 x) ≠ (nb077AlphaDummy300 x) := by
  simpa only [nb077AlphaDummy298, nb077AlphaDummy300] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_295 (x : Var) :
    (nb077AlphaDummy299 x) ≠ (nb077AlphaDummy300 x) := by
  simpa only [nb077AlphaDummy299, nb077AlphaDummy300] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_296 (F : Class) (I : Class) :
    (nb077AlphaDummy031 F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy027 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy027 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy027 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy031] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy027 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy027 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy027 F I))).fv)
      0

theorem nb077_fresh_297 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy032 x F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy029 x F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy029 x F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy029 x F I))).fv) :=
  by
  simpa only [nb077AlphaDummy032] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy029 x F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy029 x F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy029 x F I))).fv)
      0

theorem nb077_fresh_298 (F : Class) (I : Class) :
    (nb077AlphaDummy079 F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy075 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy075 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy075 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy079] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy075 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy075 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy075 F I))).fv)
      0

theorem nb077_fresh_299 (x : Var) :
    (nb077AlphaDummy080 x) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy077 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy077 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy077 x))).fv) :=
  by
  simpa only [nb077AlphaDummy080] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy077 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy077 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy077 x))).fv)
      0

theorem nb077_fresh_300 (F : Class) (I : Class) :
    (nb077AlphaDummy115 F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy111 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy111 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy111 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy115] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy111 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy111 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy111 F I))).fv)
      0

theorem nb077_fresh_301 (x : Var) :
    (nb077AlphaDummy116 x) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy113 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy113 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy113 x))).fv) :=
  by
  simpa only [nb077AlphaDummy116] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy113 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy113 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy113 x))).fv)
      0

theorem nb077_fresh_302 (F : Class) (I : Class) :
    (nb077AlphaDummy159 F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy155 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy155 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy155 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy159] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy155 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy155 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy155 F I))).fv)
      0

theorem nb077_fresh_303 (x : Var) :
    (nb077AlphaDummy160 x) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy157 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy157 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy157 x))).fv) :=
  by
  simpa only [nb077AlphaDummy160] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy157 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy157 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy157 x))).fv)
      0

theorem nb077_fresh_304 (F : Class) (I : Class) :
    (nb077AlphaDummy195 F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy191 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy191 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy191 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy195] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy191 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy191 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy191 F I))).fv)
      0

theorem nb077_fresh_305 (x : Var) :
    (nb077AlphaDummy196 x) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy193 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy193 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy193 x))).fv) :=
  by
  simpa only [nb077AlphaDummy196] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy193 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy193 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy193 x))).fv)
      0

theorem nb077_fresh_306 (F : Class) (I : Class) :
    (nb077AlphaDummy231 F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy227 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy227 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy227 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy231] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy227 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy227 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy227 F I))).fv)
      0

theorem nb077_fresh_307 (x : Var) :
    (nb077AlphaDummy232 x) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy229 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy229 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy229 x))).fv) :=
  by
  simpa only [nb077AlphaDummy232] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy229 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy229 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy229 x))).fv)
      0

theorem nb077_fresh_308 (F : Class) (I : Class) :
    (nb077AlphaDummy271 F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy267 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy267 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy267 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy271] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy267 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy267 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy267 F I))).fv)
      0

theorem nb077_fresh_309 (x : Var) :
    (nb077AlphaDummy272 x) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy269 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy269 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy269 x))).fv) :=
  by
  simpa only [nb077AlphaDummy272] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy269 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy269 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy269 x))).fv)
      0

theorem nb077_fresh_310 (F : Class) (I : Class) :
    (nb077AlphaDummy323 F I) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy319 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy319 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy319 F I))).fv) :=
  by
  simpa only [nb077AlphaDummy323] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy319 F I)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy319 F I)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy319 F I))).fv)
      0

theorem nb077_fresh_311 (x : Var) :
    (nb077AlphaDummy324 x) ∉
      (((Wff.classMem (Class.cv (nb077AlphaDummy321 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy321 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy321 x))).fv) :=
  by
  simpa only [nb077AlphaDummy324] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb077AlphaDummy321 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb077AlphaDummy321 x)) (synC1c))).fv ∪
        ((Class.cv (nb077AlphaDummy321 x))).fv)
      0

theorem nb077_fresh_312 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∉
      (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) :=
  by
  simpa only [nb077AlphaDummy059] using
    freshVar_not_mem
      (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv)
      0

theorem nb077_fresh_313 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∉
      (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) :=
  by
  simpa only [nb077AlphaDummy060] using
    freshVar_not_mem
      (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv)
      1

theorem nb077_fresh_314 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∉
      (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) :=
  by
  simpa only [nb077AlphaDummy061] using
    freshVar_not_mem
      (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv)
      2

theorem nb077_distinct_315 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy060 F I) := by
  simpa only [nb077AlphaDummy059, nb077AlphaDummy060] using
    (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom
            (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_316 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy061 F I) := by
  simpa only [nb077AlphaDummy059, nb077AlphaDummy061] using
    (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom
            (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_317 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy061 F I) := by
  simpa only [nb077AlphaDummy060, nb077AlphaDummy061] using
    (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom
            (synCmpt (nb077AlphaDummy000 F I) (synCvv)
              (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_318 (x : Var) :
    (nb077AlphaDummy062 x) ∉
      (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) :=
  by
  simpa only [nb077AlphaDummy062] using
    freshVar_not_mem
      (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv)
      0

theorem nb077_fresh_319 (x : Var) :
    (nb077AlphaDummy063 x) ∉
      (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) :=
  by
  simpa only [nb077AlphaDummy063] using
    freshVar_not_mem
      (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv)
      1

theorem nb077_fresh_320 (x : Var) :
    (nb077AlphaDummy064 x) ∉
      (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) :=
  by
  simpa only [nb077AlphaDummy064] using
    freshVar_not_mem
      (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv)
      2

theorem nb077_distinct_321 (x : Var) :
    (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy063 x) := by
  simpa only [nb077AlphaDummy062, nb077AlphaDummy063] using
    (freshVar_injective (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb077_distinct_322 (x : Var) :
    (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy064 x) := by
  simpa only [nb077AlphaDummy062, nb077AlphaDummy064] using
    (freshVar_injective (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb077_distinct_323 (x : Var) :
    (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy064 x) := by
  simpa only [nb077AlphaDummy063, nb077AlphaDummy064] using
    (freshVar_injective (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb077_fresh_324 (F : Class) (I : Class) :
    (nb077AlphaDummy057 F I) ∉
      (((synCcom (synCcnv (synC1st)) (synCcom
              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))).fv ∪
        ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv) :=
  by
  simpa only [nb077AlphaDummy057] using
    freshVar_not_mem
      (((synCcom (synCcnv (synC1st)) (synCcom
              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))).fv ∪
        ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv)
      0

theorem nb077_fresh_325 (x : Var) (F : Class) :
    (nb077AlphaDummy058 x F) ∉
      (((synCcom (synCcnv (synC1st))
            (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
              (synC1st)))).fv ∪
        ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv) :=
  by
  simpa only [nb077AlphaDummy058] using
    freshVar_not_mem
      (((synCcom (synCcnv (synC1st))
            (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
              (synC1st)))).fv ∪ ((synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))).fv)
      0

theorem nb077_fresh_326 (F : Class) (I : Class) :
    (nb077AlphaDummy023 F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCphi (Class.cv (nb077AlphaDummy020 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy023] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCphi (Class.cv (nb077AlphaDummy020 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy015 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy020 F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_327 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy024 x F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy021 x F I)
              (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy018 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCphi (Class.cv (nb077AlphaDummy022 x F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
                (Class.cv (nb077AlphaDummy017 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy024] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy021 x F I)
              (synWrex (nb077AlphaDummy022 x F I) (Class.cv (nb077AlphaDummy018 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCphi (Class.cv (nb077AlphaDummy022 x F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
                (Class.cv (nb077AlphaDummy017 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy022 x F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_328 (F : Class) (I : Class) :
    (nb077AlphaDummy071 F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCphi (Class.cv (nb077AlphaDummy068 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy071] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCphi (Class.cv (nb077AlphaDummy068 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy060 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy068 F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_329 (x : Var) :
    (nb077AlphaDummy072 x) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCphi (Class.cv (nb077AlphaDummy070 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy072] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCphi (Class.cv (nb077AlphaDummy070 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy063 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy070 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_330 (F : Class) (I : Class) :
    (nb077AlphaDummy107 F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCphi (Class.cv (nb077AlphaDummy104 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy107] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCphi (Class.cv (nb077AlphaDummy104 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy104 F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_331 (x : Var) :
    (nb077AlphaDummy108 x) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCphi (Class.cv (nb077AlphaDummy106 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy108] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCphi (Class.cv (nb077AlphaDummy106 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy106 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_332 (F : Class) (I : Class) :
    (nb077AlphaDummy151 F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCphi (Class.cv (nb077AlphaDummy148 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy151] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCphi (Class.cv (nb077AlphaDummy148 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy140 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy148 F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_333 (x : Var) :
    (nb077AlphaDummy152 x) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCphi (Class.cv (nb077AlphaDummy150 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy152] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCphi (Class.cv (nb077AlphaDummy150 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy143 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy150 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_334 (F : Class) (I : Class) :
    (nb077AlphaDummy187 F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCphi (Class.cv (nb077AlphaDummy184 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy187] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCphi (Class.cv (nb077AlphaDummy184 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy183 F I)
              (synWrex (nb077AlphaDummy184 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy183 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy184 F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_335 (x : Var) :
    (nb077AlphaDummy188 x) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCphi (Class.cv (nb077AlphaDummy186 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy188] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCphi (Class.cv (nb077AlphaDummy186 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy185 x)
              (synWrex (nb077AlphaDummy186 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy185 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy186 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_336 (F : Class) (I : Class) :
    (nb077AlphaDummy223 F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCphi (Class.cv (nb077AlphaDummy220 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy223] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy141 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCphi (Class.cv (nb077AlphaDummy220 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy219 F I)
              (synWrex (nb077AlphaDummy220 F I) (Class.cv (nb077AlphaDummy140 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy219 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy220 F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_337 (x : Var) :
    (nb077AlphaDummy224 x) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCphi (Class.cv (nb077AlphaDummy222 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy224] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy144 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCphi (Class.cv (nb077AlphaDummy222 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy221 x)
              (synWrex (nb077AlphaDummy222 x) (Class.cv (nb077AlphaDummy143 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy221 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy222 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_338 (F : Class) (I : Class) :
    (nb077AlphaDummy263 F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy259 F I)
              (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                  (synCphi (Class.cv (nb077AlphaDummy260 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy259 F I)
              (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy263] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy259 F I)
              (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy000 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                  (synCphi (Class.cv (nb077AlphaDummy260 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy259 F I)
              (synWrex (nb077AlphaDummy260 F I) (Class.cv (nb077AlphaDummy255 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy259 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy260 F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_339 (x : Var) :
    (nb077AlphaDummy264 x) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy261 x)
              (synWrex (nb077AlphaDummy262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                  (synCphi (Class.cv (nb077AlphaDummy262 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy261 x)
              (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy264] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy261 x)
              (synWrex (nb077AlphaDummy262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                  (synCphi (Class.cv (nb077AlphaDummy262 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy261 x)
              (synWrex (nb077AlphaDummy262 x) (Class.cv (nb077AlphaDummy256 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy261 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy262 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_340 (F : Class) (I : Class) :
    (nb077AlphaDummy315 F I) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCphi (Class.cv (nb077AlphaDummy312 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy315] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy061 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCphi (Class.cv (nb077AlphaDummy312 F I)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy311 F I)
              (synWrex (nb077AlphaDummy312 F I) (Class.cv (nb077AlphaDummy060 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy311 F I))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy312 F I)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_341 (x : Var) :
    (nb077AlphaDummy316 x) ∉
      (((synCcompl (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCphi (Class.cv (nb077AlphaDummy314 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb077AlphaDummy316] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy064 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCphi (Class.cv (nb077AlphaDummy314 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb077AlphaDummy313 x)
              (synWrex (nb077AlphaDummy314 x) (Class.cv (nb077AlphaDummy063 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy313 x))
                  (synCun (synCphi (Class.cv (nb077AlphaDummy314 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb077_fresh_342 (F : Class) (I : Class) :
    (nb077AlphaDummy043 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy034 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy035 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy043] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy034 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy035 F I)))).fv)
      0

theorem nb077_fresh_343 (x : Var) (F : Class) (I : Class) :
    (nb077AlphaDummy044 x F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy037 x F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy038 x F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy044] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy037 x F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy038 x F I)))).fv)
      0

theorem nb077_fresh_344 (F : Class) (I : Class) :
    (nb077AlphaDummy091 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy082 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy083 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy091] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy082 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy083 F I)))).fv)
      0

theorem nb077_fresh_345 (x : Var) :
    (nb077AlphaDummy092 x) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy085 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy086 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy092] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy085 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy086 x)))).fv)
      0

theorem nb077_fresh_346 (F : Class) (I : Class) :
    (nb077AlphaDummy127 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy118 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy119 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy127] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy118 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy119 F I)))).fv)
      0

theorem nb077_fresh_347 (x : Var) :
    (nb077AlphaDummy128 x) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy121 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy122 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy128] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy121 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy122 x)))).fv)
      0

theorem nb077_fresh_348 (F : Class) (I : Class) :
    (nb077AlphaDummy171 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy162 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy163 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy171] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy162 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy163 F I)))).fv)
      0

theorem nb077_fresh_349 (x : Var) :
    (nb077AlphaDummy172 x) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy165 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy166 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy172] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy165 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy166 x)))).fv)
      0

theorem nb077_fresh_350 (F : Class) (I : Class) :
    (nb077AlphaDummy207 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy198 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy199 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy207] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy198 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy199 F I)))).fv)
      0

theorem nb077_fresh_351 (x : Var) :
    (nb077AlphaDummy208 x) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy201 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy202 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy208] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy201 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy202 x)))).fv)
      0

theorem nb077_fresh_352 (F : Class) (I : Class) :
    (nb077AlphaDummy243 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy234 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy235 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy243] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy234 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy235 F I)))).fv)
      0

theorem nb077_fresh_353 (x : Var) :
    (nb077AlphaDummy244 x) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy237 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy238 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy244] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy237 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy238 x)))).fv)
      0

theorem nb077_fresh_354 (F : Class) (I : Class) :
    (nb077AlphaDummy283 F I) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy274 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy275 F I)))).fv) :=
  by
  simpa only [nb077AlphaDummy283] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy274 F I)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy275 F I)))).fv)
      0

theorem nb077_fresh_355 (x : Var) :
    (nb077AlphaDummy284 x) ∉
      (((synCcompl (Class.cv (nb077AlphaDummy277 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy278 x)))).fv) :=
  by
  simpa only [nb077AlphaDummy284] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb077AlphaDummy277 x)))).fv ∪
        ((synCcompl (Class.cv (nb077AlphaDummy278 x)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
