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

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_000`. -/
@[expose]
noncomputable def nb072AlphaDummy000 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_001`. -/
@[expose]
noncomputable def nb072AlphaDummy001 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_002`. -/
@[expose]
noncomputable def nb072AlphaDummy002 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_003`. -/
@[expose]
noncomputable def nb072AlphaDummy003 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_004`. -/
@[expose]
noncomputable def nb072AlphaDummy004 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_005`. -/
@[expose]
noncomputable def nb072AlphaDummy005 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_006`. -/
@[expose]
noncomputable def nb072AlphaDummy006 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))))))).fv ∪
      ((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_007`. -/
@[expose]
noncomputable def nb072AlphaDummy007 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCphi (Class.cv (nb072AlphaDummy005 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_008`. -/
@[expose]
noncomputable def nb072AlphaDummy008 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy002 A B R S_cls H)
          (synWrex (nb072AlphaDummy003 A B R S_cls H)
            (Class.cv (nb072AlphaDummy000 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
              (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))))).fv ∪
      ((Class.cab (nb072AlphaDummy002 A B R S_cls H)
          (synWrex (nb072AlphaDummy003 A B R S_cls H)
            (Class.cv (nb072AlphaDummy000 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
              (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_009`. -/
@[expose]
noncomputable def nb072AlphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy004 x y)
          (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
              (synCphi (Class.cv (nb072AlphaDummy005 x y))))))).fv ∪
      ((Class.cab (nb072AlphaDummy004 x y) (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
              (synCphi (Class.cv (nb072AlphaDummy005 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_010`. -/
@[expose]
noncomputable def nb072AlphaDummy010 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_011`. -/
@[expose]
noncomputable def nb072AlphaDummy011 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_012`. -/
@[expose]
noncomputable def nb072AlphaDummy012 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy005 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_013`. -/
@[expose]
noncomputable def nb072AlphaDummy013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy005 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_014`. -/
@[expose]
noncomputable def nb072AlphaDummy014 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072AlphaDummy010 A B R S_cls H)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb072AlphaDummy010 A B R S_cls H)) (synC1c))).fv ∪
      ((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_015`. -/
@[expose]
noncomputable def nb072AlphaDummy015 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072AlphaDummy012 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb072AlphaDummy012 x y)) (synC1c))).fv ∪
      ((Class.cv (nb072AlphaDummy012 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_016`. -/
@[expose]
noncomputable def nb072AlphaDummy016 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_017`. -/
@[expose]
noncomputable def nb072AlphaDummy017 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_018`. -/
@[expose]
noncomputable def nb072AlphaDummy018 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_019`. -/
@[expose]
noncomputable def nb072AlphaDummy019 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_020`. -/
@[expose]
noncomputable def nb072AlphaDummy020 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_021`. -/
@[expose]
noncomputable def nb072AlphaDummy021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_022`. -/
@[expose]
noncomputable def nb072AlphaDummy022 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
          (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv ∪
      ((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
          (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_023`. -/
@[expose]
noncomputable def nb072AlphaDummy023 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb072AlphaDummy020 x y))
          (Class.cv (nb072AlphaDummy021 x y)))).fv ∪
      ((synCnin (Class.cv (nb072AlphaDummy020 x y))
          (Class.cv (nb072AlphaDummy021 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_024`. -/
@[expose]
noncomputable def nb072AlphaDummy024 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_025`. -/
@[expose]
noncomputable def nb072AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
      ((Class.cv (nb072AlphaDummy021 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_026`. -/
@[expose]
noncomputable def nb072AlphaDummy026 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb072AlphaDummy017 A B R S_cls H)))).fv ∪
      ((synCcompl (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_027`. -/
@[expose]
noncomputable def nb072AlphaDummy027 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb072AlphaDummy020 x y)))).fv ∪
      ((synCcompl (Class.cv (nb072AlphaDummy021 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_028`. -/
@[expose]
noncomputable def nb072AlphaDummy028 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_029`. -/
@[expose]
noncomputable def nb072AlphaDummy029 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
      ((Class.cv (nb072AlphaDummy020 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_030`. -/
@[expose]
noncomputable def nb072AlphaDummy030 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_031`. -/
@[expose]
noncomputable def nb072AlphaDummy031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy021 x y))).fv ∪
      ((Class.cv (nb072AlphaDummy021 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_032`. -/
@[expose]
noncomputable def nb072AlphaDummy032 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy002 A B R S_cls H)
          (synWrex (nb072AlphaDummy003 A B R S_cls H)
            (Class.cv (nb072AlphaDummy001 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy002 A B R S_cls H)
          (synWrex (nb072AlphaDummy003 A B R S_cls H)
            (Class.cv (nb072AlphaDummy001 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_033`. -/
@[expose]
noncomputable def nb072AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy004 x y)
          (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
              (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy004 x y)
          (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
              (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_034`. -/
@[expose]
noncomputable def nb072AlphaDummy034 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_035`. -/
@[expose]
noncomputable def nb072AlphaDummy035 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb072AlphaDummy005 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_036`. -/
@[expose]
noncomputable def nb072AlphaDummy036 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))).fv ∪
      ((synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_037`. -/
@[expose]
noncomputable def nb072AlphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb072AlphaDummy005 x y)))).fv ∪
      ((synCphi (Class.cv (nb072AlphaDummy005 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_038`. -/
@[expose]
noncomputable def nb072AlphaDummy038 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
      ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_039`. -/
@[expose]
noncomputable def nb072AlphaDummy039 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
      ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_040`. -/
@[expose]
noncomputable def nb072AlphaDummy040 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_041`. -/
@[expose]
noncomputable def nb072AlphaDummy041 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_042`. -/
@[expose]
noncomputable def nb072AlphaDummy042 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))))).fv ∪
      ((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_043`. -/
@[expose]
noncomputable def nb072AlphaDummy043 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCphi (Class.cv (nb072AlphaDummy041 x y H)))))))).fv ∪ ((synCcompl
          (Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_044`. -/
@[expose]
noncomputable def nb072AlphaDummy044 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
          (synWrex (nb072AlphaDummy039 A B R S_cls H)
            (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
            (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
              (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv ∪
      ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
          (synWrex (nb072AlphaDummy039 A B R S_cls H)
            (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
            (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
              (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_045`. -/
@[expose]
noncomputable def nb072AlphaDummy045 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy040 x y H)
          (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
            (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
              (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv ∪
      ((Class.cab (nb072AlphaDummy040 x y H)
          (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
            (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
              (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_046`. -/
@[expose]
noncomputable def nb072AlphaDummy046 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar ((H).fv ∪ ((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_047`. -/
@[expose]
noncomputable def nb072AlphaDummy047 (x : Var) (H : Class) : Var :=
  (freshVar ((H).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_048`. -/
@[expose]
noncomputable def nb072AlphaDummy048 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (({(nb072AlphaDummy046 A B R S_cls H)} : Finset Var) ∪
      ((synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
          (Class.cv (nb072AlphaDummy046 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_049`. -/
@[expose]
noncomputable def nb072AlphaDummy049 (x : Var) (H : Class) : Var :=
  (freshVar (({(nb072AlphaDummy047 x H)} : Finset Var) ∪
      ((synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_050`. -/
@[expose]
noncomputable def nb072AlphaDummy050 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
          (Class.cab (nb072AlphaDummy046 A B R S_cls H)
            (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
          (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_051`. -/
@[expose]
noncomputable def nb072AlphaDummy051 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
          (Class.cab (nb072AlphaDummy046 A B R S_cls H)
            (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
          (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_052`. -/
@[expose]
noncomputable def nb072AlphaDummy052 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
          (Class.cab (nb072AlphaDummy047 x H)
            (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
          (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_053`. -/
@[expose]
noncomputable def nb072AlphaDummy053 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
          (Class.cab (nb072AlphaDummy047 x H)
            (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
          (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_054`. -/
@[expose]
noncomputable def nb072AlphaDummy054 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_055`. -/
@[expose]
noncomputable def nb072AlphaDummy055 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_056`. -/
@[expose]
noncomputable def nb072AlphaDummy056 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_057`. -/
@[expose]
noncomputable def nb072AlphaDummy057 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_058`. -/
@[expose]
noncomputable def nb072AlphaDummy058 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))))))).fv ∪
      ((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_059`. -/
@[expose]
noncomputable def nb072AlphaDummy059 (x : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCphi (Class.cv (nb072AlphaDummy057 x H)))))))).fv ∪ ((synCcompl
          (Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_060`. -/
@[expose]
noncomputable def nb072AlphaDummy060 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy054 A B R S_cls H)
          (synWrex (nb072AlphaDummy055 A B R S_cls H)
            (Class.cv (nb072AlphaDummy000 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
              (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))).fv ∪
      ((Class.cab (nb072AlphaDummy054 A B R S_cls H)
          (synWrex (nb072AlphaDummy055 A B R S_cls H)
            (Class.cv (nb072AlphaDummy000 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
              (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_061`. -/
@[expose]
noncomputable def nb072AlphaDummy061 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy056 x H)
          (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
            (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
              (synCphi (Class.cv (nb072AlphaDummy057 x H))))))).fv ∪
      ((Class.cab (nb072AlphaDummy056 x H) (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
            (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
              (synCphi (Class.cv (nb072AlphaDummy057 x H))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_062`. -/
@[expose]
noncomputable def nb072AlphaDummy062 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_063`. -/
@[expose]
noncomputable def nb072AlphaDummy063 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_064`. -/
@[expose]
noncomputable def nb072AlphaDummy064 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy057 x H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_065`. -/
@[expose]
noncomputable def nb072AlphaDummy065 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy057 x H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_066`. -/
@[expose]
noncomputable def nb072AlphaDummy066 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072AlphaDummy062 A B R S_cls H)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb072AlphaDummy062 A B R S_cls H)) (synC1c))).fv ∪
      ((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_067`. -/
@[expose]
noncomputable def nb072AlphaDummy067 (x : Var) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072AlphaDummy064 x H)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb072AlphaDummy064 x H)) (synC1c))).fv ∪
      ((Class.cv (nb072AlphaDummy064 x H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_068`. -/
@[expose]
noncomputable def nb072AlphaDummy068 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_069`. -/
@[expose]
noncomputable def nb072AlphaDummy069 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_070`. -/
@[expose]
noncomputable def nb072AlphaDummy070 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_071`. -/
@[expose]
noncomputable def nb072AlphaDummy071 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_072`. -/
@[expose]
noncomputable def nb072AlphaDummy072 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_073`. -/
@[expose]
noncomputable def nb072AlphaDummy073 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_074`. -/
@[expose]
noncomputable def nb072AlphaDummy074 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
          (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv ∪
      ((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
          (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_075`. -/
@[expose]
noncomputable def nb072AlphaDummy075 (x : Var) (H : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb072AlphaDummy072 x H))
          (Class.cv (nb072AlphaDummy073 x H)))).fv ∪
      ((synCnin (Class.cv (nb072AlphaDummy072 x H))
          (Class.cv (nb072AlphaDummy073 x H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_076`. -/
@[expose]
noncomputable def nb072AlphaDummy076 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_077`. -/
@[expose]
noncomputable def nb072AlphaDummy077 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
      ((Class.cv (nb072AlphaDummy073 x H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_078`. -/
@[expose]
noncomputable def nb072AlphaDummy078 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb072AlphaDummy069 A B R S_cls H)))).fv ∪
      ((synCcompl (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_079`. -/
@[expose]
noncomputable def nb072AlphaDummy079 (x : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb072AlphaDummy072 x H)))).fv ∪
      ((synCcompl (Class.cv (nb072AlphaDummy073 x H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_080`. -/
@[expose]
noncomputable def nb072AlphaDummy080 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_081`. -/
@[expose]
noncomputable def nb072AlphaDummy081 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
      ((Class.cv (nb072AlphaDummy072 x H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_082`. -/
@[expose]
noncomputable def nb072AlphaDummy082 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_083`. -/
@[expose]
noncomputable def nb072AlphaDummy083 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy073 x H))).fv ∪
      ((Class.cv (nb072AlphaDummy073 x H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_084`. -/
@[expose]
noncomputable def nb072AlphaDummy084 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy054 A B R S_cls H)
          (synWrex (nb072AlphaDummy055 A B R S_cls H)
            (Class.cv (nb072AlphaDummy046 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy054 A B R S_cls H)
          (synWrex (nb072AlphaDummy055 A B R S_cls H)
            (Class.cv (nb072AlphaDummy046 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_085`. -/
@[expose]
noncomputable def nb072AlphaDummy085 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy056 x H)
          (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
            (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy056 x H)
          (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
            (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_086`. -/
@[expose]
noncomputable def nb072AlphaDummy086 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_087`. -/
@[expose]
noncomputable def nb072AlphaDummy087 (x : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb072AlphaDummy057 x H))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_088`. -/
@[expose]
noncomputable def nb072AlphaDummy088 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))).fv ∪
      ((synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_089`. -/
@[expose]
noncomputable def nb072AlphaDummy089 (x : Var) (H : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb072AlphaDummy057 x H)))).fv ∪
      ((synCphi (Class.cv (nb072AlphaDummy057 x H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_090`. -/
@[expose]
noncomputable def nb072AlphaDummy090 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy048 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_091`. -/
@[expose]
noncomputable def nb072AlphaDummy091 (x : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy049 x H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_092`. -/
@[expose]
noncomputable def nb072AlphaDummy092 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_093`. -/
@[expose]
noncomputable def nb072AlphaDummy093 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_094`. -/
@[expose]
noncomputable def nb072AlphaDummy094 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy041 x y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_095`. -/
@[expose]
noncomputable def nb072AlphaDummy095 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy041 x y H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_096`. -/
@[expose]
noncomputable def nb072AlphaDummy096 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072AlphaDummy092 A B R S_cls H)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb072AlphaDummy092 A B R S_cls H)) (synC1c))).fv ∪
      ((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_097`. -/
@[expose]
noncomputable def nb072AlphaDummy097 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072AlphaDummy094 x y H)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb072AlphaDummy094 x y H)) (synC1c))).fv ∪
      ((Class.cv (nb072AlphaDummy094 x y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_098`. -/
@[expose]
noncomputable def nb072AlphaDummy098 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_099`. -/
@[expose]
noncomputable def nb072AlphaDummy099 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_100`. -/
@[expose]
noncomputable def nb072AlphaDummy100 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_101`. -/
@[expose]
noncomputable def nb072AlphaDummy101 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_102`. -/
@[expose]
noncomputable def nb072AlphaDummy102 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_103`. -/
@[expose]
noncomputable def nb072AlphaDummy103 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_104`. -/
@[expose]
noncomputable def nb072AlphaDummy104 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
          (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv ∪
      ((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
          (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_105`. -/
@[expose]
noncomputable def nb072AlphaDummy105 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb072AlphaDummy102 x y H))
          (Class.cv (nb072AlphaDummy103 x y H)))).fv ∪
      ((synCnin (Class.cv (nb072AlphaDummy102 x y H))
          (Class.cv (nb072AlphaDummy103 x y H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_106`. -/
@[expose]
noncomputable def nb072AlphaDummy106 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_107`. -/
@[expose]
noncomputable def nb072AlphaDummy107 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
      ((Class.cv (nb072AlphaDummy103 x y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_108`. -/
@[expose]
noncomputable def nb072AlphaDummy108 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb072AlphaDummy099 A B R S_cls H)))).fv ∪
      ((synCcompl (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_109`. -/
@[expose]
noncomputable def nb072AlphaDummy109 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb072AlphaDummy102 x y H)))).fv ∪
      ((synCcompl (Class.cv (nb072AlphaDummy103 x y H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_110`. -/
@[expose]
noncomputable def nb072AlphaDummy110 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_111`. -/
@[expose]
noncomputable def nb072AlphaDummy111 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
      ((Class.cv (nb072AlphaDummy102 x y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_112`. -/
@[expose]
noncomputable def nb072AlphaDummy112 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_113`. -/
@[expose]
noncomputable def nb072AlphaDummy113 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy103 x y H))).fv ∪
      ((Class.cv (nb072AlphaDummy103 x y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_114`. -/
@[expose]
noncomputable def nb072AlphaDummy114 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
          (synWrex (nb072AlphaDummy039 A B R S_cls H)
            (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
            (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
          (synWrex (nb072AlphaDummy039 A B R S_cls H)
            (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
            (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_115`. -/
@[expose]
noncomputable def nb072AlphaDummy115 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy040 x y H)
          (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
            (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy040 x y H)
          (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
            (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_116`. -/
@[expose]
noncomputable def nb072AlphaDummy116 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar ((H).fv ∪ ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_117`. -/
@[expose]
noncomputable def nb072AlphaDummy117 (y : Var) (H : Class) : Var :=
  (freshVar ((H).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_118`. -/
@[expose]
noncomputable def nb072AlphaDummy118 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (({(nb072AlphaDummy116 A B R S_cls H)} : Finset Var) ∪
      ((synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
          (Class.cv (nb072AlphaDummy116 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_119`. -/
@[expose]
noncomputable def nb072AlphaDummy119 (y : Var) (H : Class) : Var :=
  (freshVar (({(nb072AlphaDummy117 y H)} : Finset Var) ∪
      ((synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_120`. -/
@[expose]
noncomputable def nb072AlphaDummy120 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
          (Class.cab (nb072AlphaDummy116 A B R S_cls H)
            (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
          (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_121`. -/
@[expose]
noncomputable def nb072AlphaDummy121 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
          (Class.cab (nb072AlphaDummy116 A B R S_cls H)
            (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
          (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_122`. -/
@[expose]
noncomputable def nb072AlphaDummy122 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy119 y H) (Wff.classEq
          (Class.cab (nb072AlphaDummy117 y H)
            (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
          (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_123`. -/
@[expose]
noncomputable def nb072AlphaDummy123 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy119 y H) (Wff.classEq
          (Class.cab (nb072AlphaDummy117 y H)
            (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
          (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_124`. -/
@[expose]
noncomputable def nb072AlphaDummy124 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_125`. -/
@[expose]
noncomputable def nb072AlphaDummy125 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_126`. -/
@[expose]
noncomputable def nb072AlphaDummy126 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_127`. -/
@[expose]
noncomputable def nb072AlphaDummy127 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_128`. -/
@[expose]
noncomputable def nb072AlphaDummy128 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))))))).fv ∪
      ((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_129`. -/
@[expose]
noncomputable def nb072AlphaDummy129 (y : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCphi (Class.cv (nb072AlphaDummy127 y H)))))))).fv ∪ ((synCcompl
          (Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_130`. -/
@[expose]
noncomputable def nb072AlphaDummy130 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy124 A B R S_cls H)
          (synWrex (nb072AlphaDummy125 A B R S_cls H)
            (Class.cv (nb072AlphaDummy001 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
              (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))).fv ∪
      ((Class.cab (nb072AlphaDummy124 A B R S_cls H)
          (synWrex (nb072AlphaDummy125 A B R S_cls H)
            (Class.cv (nb072AlphaDummy001 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
              (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_131`. -/
@[expose]
noncomputable def nb072AlphaDummy131 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy126 y H)
          (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
            (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
              (synCphi (Class.cv (nb072AlphaDummy127 y H))))))).fv ∪
      ((Class.cab (nb072AlphaDummy126 y H) (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
            (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
              (synCphi (Class.cv (nb072AlphaDummy127 y H))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_132`. -/
@[expose]
noncomputable def nb072AlphaDummy132 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_133`. -/
@[expose]
noncomputable def nb072AlphaDummy133 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_134`. -/
@[expose]
noncomputable def nb072AlphaDummy134 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy127 y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_135`. -/
@[expose]
noncomputable def nb072AlphaDummy135 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy127 y H))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_136`. -/
@[expose]
noncomputable def nb072AlphaDummy136 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072AlphaDummy132 A B R S_cls H)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb072AlphaDummy132 A B R S_cls H)) (synC1c))).fv ∪
      ((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_137`. -/
@[expose]
noncomputable def nb072AlphaDummy137 (y : Var) (H : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb072AlphaDummy134 y H)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb072AlphaDummy134 y H)) (synC1c))).fv ∪
      ((Class.cv (nb072AlphaDummy134 y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_138`. -/
@[expose]
noncomputable def nb072AlphaDummy138 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_139`. -/
@[expose]
noncomputable def nb072AlphaDummy139 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_140`. -/
@[expose]
noncomputable def nb072AlphaDummy140 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_141`. -/
@[expose]
noncomputable def nb072AlphaDummy141 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_142`. -/
@[expose]
noncomputable def nb072AlphaDummy142 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_143`. -/
@[expose]
noncomputable def nb072AlphaDummy143 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_144`. -/
@[expose]
noncomputable def nb072AlphaDummy144 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
          (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv ∪
      ((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
          (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_145`. -/
@[expose]
noncomputable def nb072AlphaDummy145 (y : Var) (H : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb072AlphaDummy142 y H))
          (Class.cv (nb072AlphaDummy143 y H)))).fv ∪
      ((synCnin (Class.cv (nb072AlphaDummy142 y H))
          (Class.cv (nb072AlphaDummy143 y H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_146`. -/
@[expose]
noncomputable def nb072AlphaDummy146 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_147`. -/
@[expose]
noncomputable def nb072AlphaDummy147 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
      ((Class.cv (nb072AlphaDummy143 y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_148`. -/
@[expose]
noncomputable def nb072AlphaDummy148 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb072AlphaDummy139 A B R S_cls H)))).fv ∪
      ((synCcompl (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_149`. -/
@[expose]
noncomputable def nb072AlphaDummy149 (y : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb072AlphaDummy142 y H)))).fv ∪
      ((synCcompl (Class.cv (nb072AlphaDummy143 y H)))).fv) 0)

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

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_150`. -/
@[expose]
noncomputable def nb072AlphaDummy150 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_151`. -/
@[expose]
noncomputable def nb072AlphaDummy151 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
      ((Class.cv (nb072AlphaDummy142 y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_152`. -/
@[expose]
noncomputable def nb072AlphaDummy152 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv ∪
      ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_153`. -/
@[expose]
noncomputable def nb072AlphaDummy153 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy143 y H))).fv ∪
      ((Class.cv (nb072AlphaDummy143 y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_154`. -/
@[expose]
noncomputable def nb072AlphaDummy154 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy124 A B R S_cls H)
          (synWrex (nb072AlphaDummy125 A B R S_cls H)
            (Class.cv (nb072AlphaDummy116 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy124 A B R S_cls H)
          (synWrex (nb072AlphaDummy125 A B R S_cls H)
            (Class.cv (nb072AlphaDummy116 A B R S_cls H))
            (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_155`. -/
@[expose]
noncomputable def nb072AlphaDummy155 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cab (nb072AlphaDummy126 y H)
          (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
            (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy126 y H)
          (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
            (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
              (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_156`. -/
@[expose]
noncomputable def nb072AlphaDummy156 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_157`. -/
@[expose]
noncomputable def nb072AlphaDummy157 (y : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb072AlphaDummy127 y H))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_158`. -/
@[expose]
noncomputable def nb072AlphaDummy158 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))).fv ∪
      ((synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_159`. -/
@[expose]
noncomputable def nb072AlphaDummy159 (y : Var) (H : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb072AlphaDummy127 y H)))).fv ∪
      ((synCphi (Class.cv (nb072AlphaDummy127 y H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_160`. -/
@[expose]
noncomputable def nb072AlphaDummy160 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy118 A B R S_cls H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_161`. -/
@[expose]
noncomputable def nb072AlphaDummy161 (y : Var) (H : Class) : Var :=
  (freshVar (((Class.cv (nb072AlphaDummy119 y H))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_162`. -/
@[expose]
noncomputable def nb072AlphaDummy162 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_163`. -/
@[expose]
noncomputable def nb072AlphaDummy163 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb072AlphaDummy041 x y H))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_164`. -/
@[expose]
noncomputable def nb072AlphaDummy164 (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))).fv ∪
      ((synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb072_alpha_dummy_165`. -/
@[expose]
noncomputable def nb072AlphaDummy165 (x : Var) (y : Var) (H : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb072AlphaDummy041 x y H)))).fv ∪
      ((synCphi (Class.cv (nb072AlphaDummy041 x y H)))).fv) 0)

theorem nb072_fresh_000 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy008 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))))).fv) :=
  by
  simpa only [nb072AlphaDummy008] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))))).fv)
      0

theorem nb072_fresh_001 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy032 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb072AlphaDummy032] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb072_fresh_002 (x : Var) (y : Var) :
    (nb072AlphaDummy009 x y) ∉
      (((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCphi (Class.cv (nb072AlphaDummy005 x y))))))).fv ∪
        ((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCphi (Class.cv (nb072AlphaDummy005 x y))))))).fv) :=
  by
  simpa only [nb072AlphaDummy009] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCphi (Class.cv (nb072AlphaDummy005 x y))))))).fv ∪
        ((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCphi (Class.cv (nb072AlphaDummy005 x y))))))).fv)
      0

theorem nb072_fresh_003 (x : Var) (y : Var) :
    (nb072AlphaDummy033 x y) ∉
      (((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb072AlphaDummy033] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb072_fresh_004 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy044 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv) :=
  by
  simpa only [nb072AlphaDummy044] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv)
      0

theorem nb072_fresh_005 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy114 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb072AlphaDummy114] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb072_fresh_006 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy045 x y H) ∉
      (((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv) :=
  by
  simpa only [nb072AlphaDummy045] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv)
      0

theorem nb072_fresh_007 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy115 x y H) ∉
      (((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb072AlphaDummy115] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb072_fresh_008 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy050 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy046 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv) :=
  by
  simpa only [nb072AlphaDummy050] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy046 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv)
      0

theorem nb072_fresh_009 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy051 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy046 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv) :=
  by
  simpa only [nb072AlphaDummy051] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy046 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv)
      1

theorem nb072_distinct_010 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy050 A B R S_cls H) ≠ (nb072AlphaDummy051 A B R S_cls H) := by
  simpa only [nb072AlphaDummy050, nb072AlphaDummy051] using
    (freshVar_injective (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy046 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_011 (x : Var) (H : Class) :
    (nb072AlphaDummy052 x H) ∉
      (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
            (Class.cab (nb072AlphaDummy047 x H)
              (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
            (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv) :=
  by
  simpa only [nb072AlphaDummy052] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
            (Class.cab (nb072AlphaDummy047 x H)
              (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
            (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv)
      0

theorem nb072_fresh_012 (x : Var) (H : Class) :
    (nb072AlphaDummy053 x H) ∉
      (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
            (Class.cab (nb072AlphaDummy047 x H)
              (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
            (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv) :=
  by
  simpa only [nb072AlphaDummy053] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
            (Class.cab (nb072AlphaDummy047 x H)
              (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
            (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv)
      1

theorem nb072_distinct_013 (x : Var) (H : Class) :
    (nb072AlphaDummy052 x H) ≠ (nb072AlphaDummy053 x H) := by
  simpa only [nb072AlphaDummy052, nb072AlphaDummy053] using
    (freshVar_injective (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
            (Class.cab (nb072AlphaDummy047 x H)
              (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
            (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_014 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy060 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))).fv) :=
  by
  simpa only [nb072AlphaDummy060] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))).fv)
      0

theorem nb072_fresh_015 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy084 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb072AlphaDummy084] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb072_fresh_016 (x : Var) (H : Class) :
    (nb072AlphaDummy085 x H) ∉
      (((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb072AlphaDummy085] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb072_fresh_017 (x : Var) (H : Class) :
    (nb072AlphaDummy061 x H) ∉
      (((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCphi (Class.cv (nb072AlphaDummy057 x H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCphi (Class.cv (nb072AlphaDummy057 x H))))))).fv) :=
  by
  simpa only [nb072AlphaDummy061] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCphi (Class.cv (nb072AlphaDummy057 x H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCphi (Class.cv (nb072AlphaDummy057 x H))))))).fv)
      0

theorem nb072_fresh_018 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy120 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy116 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv) :=
  by
  simpa only [nb072AlphaDummy120] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy116 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv)
      0

theorem nb072_fresh_019 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy121 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy116 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv) :=
  by
  simpa only [nb072AlphaDummy121] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy116 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv)
      1

theorem nb072_distinct_020 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy120 A B R S_cls H) ≠ (nb072AlphaDummy121 A B R S_cls H) := by
  simpa only [nb072AlphaDummy120, nb072AlphaDummy121] using
    (freshVar_injective (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy116 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_021 (y : Var) (H : Class) :
    (nb072AlphaDummy122 y H) ∉
      (((Class.cab (nb072AlphaDummy119 y H) (Wff.classEq
            (Class.cab (nb072AlphaDummy117 y H)
              (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
            (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv) :=
  by
  simpa only [nb072AlphaDummy122] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy119 y H) (Wff.classEq
            (Class.cab (nb072AlphaDummy117 y H)
              (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
            (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv)
      0

theorem nb072_fresh_022 (y : Var) (H : Class) :
    (nb072AlphaDummy123 y H) ∉
      (((Class.cab (nb072AlphaDummy119 y H) (Wff.classEq
            (Class.cab (nb072AlphaDummy117 y H)
              (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
            (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv) :=
  by
  simpa only [nb072AlphaDummy123] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy119 y H) (Wff.classEq
            (Class.cab (nb072AlphaDummy117 y H)
              (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
            (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv)
      1

theorem nb072_distinct_023 (y : Var) (H : Class) :
    (nb072AlphaDummy122 y H) ≠ (nb072AlphaDummy123 y H) := by
  simpa only [nb072AlphaDummy122, nb072AlphaDummy123] using
    (freshVar_injective (((Class.cab (nb072AlphaDummy119 y H) (Wff.classEq
            (Class.cab (nb072AlphaDummy117 y H)
              (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
            (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_024 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy130 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))).fv) :=
  by
  simpa only [nb072AlphaDummy130] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))).fv)
      0

theorem nb072_fresh_025 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy154 A B R S_cls H) ∉
      (((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb072AlphaDummy154] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb072_fresh_026 (y : Var) (H : Class) :
    (nb072AlphaDummy155 y H) ∉
      (((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb072AlphaDummy155] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb072_fresh_027 (y : Var) (H : Class) :
    (nb072AlphaDummy131 y H) ∉
      (((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCphi (Class.cv (nb072AlphaDummy127 y H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCphi (Class.cv (nb072AlphaDummy127 y H))))))).fv) :=
  by
  simpa only [nb072AlphaDummy131] using
    freshVar_not_mem
      (((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCphi (Class.cv (nb072AlphaDummy127 y H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCphi (Class.cv (nb072AlphaDummy127 y H))))))).fv)
      0

theorem nb072_fresh_028 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy002 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy002] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv)
      0

theorem nb072_fresh_029 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy003 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy003] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv)
      1

theorem nb072_distinct_030 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy002 A B R S_cls H) ≠ (nb072AlphaDummy003 A B R S_cls H) := by
  simpa only [nb072AlphaDummy002, nb072AlphaDummy003] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_031 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy054 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy054] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv)
      0

theorem nb072_fresh_032 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy055 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy055] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv)
      1

theorem nb072_distinct_033 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy054 A B R S_cls H) ≠ (nb072AlphaDummy055 A B R S_cls H) := by
  simpa only [nb072AlphaDummy054, nb072AlphaDummy055] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_034 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy124 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy124] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv)
      0

theorem nb072_fresh_035 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy125 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy125] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv)
      1

theorem nb072_distinct_036 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy124 A B R S_cls H) ≠ (nb072AlphaDummy125 A B R S_cls H) := by
  simpa only [nb072AlphaDummy124, nb072AlphaDummy125] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_037 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy010 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy010] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) 0

theorem nb072_fresh_038 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy011 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy011] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) 1

theorem nb072_distinct_039 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy011 A B R S_cls H) := by
  simpa only [nb072AlphaDummy010, nb072AlphaDummy011] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_fresh_040 (x : Var) (y : Var) :
    (nb072AlphaDummy012 x y) ∉ (((Class.cv (nb072AlphaDummy005 x y))).fv) := by
  simpa only [nb072AlphaDummy012] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy005 x y))).fv) 0

theorem nb072_fresh_041 (x : Var) (y : Var) :
    (nb072AlphaDummy013 x y) ∉ (((Class.cv (nb072AlphaDummy005 x y))).fv) := by
  simpa only [nb072AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy005 x y))).fv) 1

theorem nb072_distinct_042 (x : Var) (y : Var) :
    (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy013 x y) := by
  simpa only [nb072AlphaDummy012, nb072AlphaDummy013] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy005 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_043 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy016 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy016] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) 0

theorem nb072_fresh_044 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy017 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy017] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) 1

theorem nb072_fresh_045 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy018 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy018] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) 2

theorem nb072_distinct_046 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy016 A B R S_cls H) ≠ (nb072AlphaDummy017 A B R S_cls H) := by
  simpa only [nb072AlphaDummy016, nb072AlphaDummy017] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_distinct_047 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy016 A B R S_cls H) ≠ (nb072AlphaDummy018 A B R S_cls H) := by
  simpa only [nb072AlphaDummy016, nb072AlphaDummy018] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb072_distinct_048 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy018 A B R S_cls H) := by
  simpa only [nb072AlphaDummy017, nb072AlphaDummy018] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb072_fresh_049 (x : Var) (y : Var) :
    (nb072AlphaDummy019 x y) ∉
      (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb072_fresh_050 (x : Var) (y : Var) :
    (nb072AlphaDummy020 x y) ∉
      (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb072_fresh_051 (x : Var) (y : Var) :
    (nb072AlphaDummy021 x y) ∉
      (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb072_distinct_052 (x : Var) (y : Var) :
    (nb072AlphaDummy019 x y) ≠ (nb072AlphaDummy020 x y) := by
  simpa only [nb072AlphaDummy019, nb072AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_distinct_053 (x : Var) (y : Var) :
    (nb072AlphaDummy019 x y) ≠ (nb072AlphaDummy021 x y) := by
  simpa only [nb072AlphaDummy019, nb072AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb072_distinct_054 (x : Var) (y : Var) :
    (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy021 x y) := by
  simpa only [nb072AlphaDummy020, nb072AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb072_fresh_055 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy028 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv)
      0

theorem nb072_fresh_056 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy024 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy024] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv)
      0

theorem nb072_fresh_057 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy030 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv)
      0

theorem nb072_fresh_058 (x : Var) (y : Var) :
    (nb072AlphaDummy029 x y) ∉
      (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy020 x y))).fv) :=
  by
  simpa only [nb072AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy020 x y))).fv)
      0

theorem nb072_fresh_059 (x : Var) (y : Var) :
    (nb072AlphaDummy025 x y) ∉
      (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy021 x y))).fv) :=
  by
  simpa only [nb072AlphaDummy025] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy021 x y))).fv)
      0

theorem nb072_fresh_060 (x : Var) (y : Var) :
    (nb072AlphaDummy031 x y) ∉
      (((Class.cv (nb072AlphaDummy021 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy021 x y))).fv) :=
  by
  simpa only [nb072AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy021 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy021 x y))).fv)
      0

theorem nb072_fresh_061 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy092 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy092] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) 0

theorem nb072_fresh_062 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy093 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy093] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) 1

theorem nb072_distinct_063 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy092 A B R S_cls H) ≠ (nb072AlphaDummy093 A B R S_cls H) := by
  simpa only [nb072AlphaDummy092, nb072AlphaDummy093] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_fresh_064 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy094 x y H) ∉ (((Class.cv (nb072AlphaDummy041 x y H))).fv) := by
  simpa only [nb072AlphaDummy094] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy041 x y H))).fv) 0

theorem nb072_fresh_065 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy095 x y H) ∉ (((Class.cv (nb072AlphaDummy041 x y H))).fv) := by
  simpa only [nb072AlphaDummy095] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy041 x y H))).fv) 1

theorem nb072_distinct_066 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy095 x y H) := by
  simpa only [nb072AlphaDummy094, nb072AlphaDummy095] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy041 x y H))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_067 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy090 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy048 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy090] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy048 A B R S_cls H))).fv) 0

theorem nb072_fresh_068 (x : Var) (H : Class) :
    (nb072AlphaDummy091 x H) ∉ (((Class.cv (nb072AlphaDummy049 x H))).fv) := by
  simpa only [nb072AlphaDummy091] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy049 x H))).fv) 0

theorem nb072_fresh_069 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy062 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) 0

theorem nb072_fresh_070 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy063 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) 1

theorem nb072_distinct_071 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy062 A B R S_cls H) ≠ (nb072AlphaDummy063 A B R S_cls H) := by
  simpa only [nb072AlphaDummy062, nb072AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_fresh_072 (x : Var) (H : Class) :
    (nb072AlphaDummy064 x H) ∉ (((Class.cv (nb072AlphaDummy057 x H))).fv) := by
  simpa only [nb072AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy057 x H))).fv) 0

theorem nb072_fresh_073 (x : Var) (H : Class) :
    (nb072AlphaDummy065 x H) ∉ (((Class.cv (nb072AlphaDummy057 x H))).fv) := by
  simpa only [nb072AlphaDummy065] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy057 x H))).fv) 1

theorem nb072_distinct_074 (x : Var) (H : Class) :
    (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy065 x H) := by
  simpa only [nb072AlphaDummy064, nb072AlphaDummy065] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy057 x H))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_075 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy068 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) 0

theorem nb072_fresh_076 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy069 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) 1

theorem nb072_fresh_077 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy070 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) 2

theorem nb072_distinct_078 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy068 A B R S_cls H) ≠ (nb072AlphaDummy069 A B R S_cls H) := by
  simpa only [nb072AlphaDummy068, nb072AlphaDummy069] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_distinct_079 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy068 A B R S_cls H) ≠ (nb072AlphaDummy070 A B R S_cls H) := by
  simpa only [nb072AlphaDummy068, nb072AlphaDummy070] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb072_distinct_080 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy070 A B R S_cls H) := by
  simpa only [nb072AlphaDummy069, nb072AlphaDummy070] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb072_fresh_081 (x : Var) (H : Class) :
    (nb072AlphaDummy071 x H) ∉
      (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy071] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) 0

theorem nb072_fresh_082 (x : Var) (H : Class) :
    (nb072AlphaDummy072 x H) ∉
      (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy072] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) 1

theorem nb072_fresh_083 (x : Var) (H : Class) :
    (nb072AlphaDummy073 x H) ∉
      (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy073] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) 2

theorem nb072_distinct_084 (x : Var) (H : Class) :
    (nb072AlphaDummy071 x H) ≠ (nb072AlphaDummy072 x H) := by
  simpa only [nb072AlphaDummy071, nb072AlphaDummy072] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_distinct_085 (x : Var) (H : Class) :
    (nb072AlphaDummy071 x H) ≠ (nb072AlphaDummy073 x H) := by
  simpa only [nb072AlphaDummy071, nb072AlphaDummy073] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb072_distinct_086 (x : Var) (H : Class) :
    (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy073 x H) := by
  simpa only [nb072AlphaDummy072, nb072AlphaDummy073] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb072_fresh_087 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy080 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv)
      0

theorem nb072_fresh_088 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy076 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy076] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv)
      0

theorem nb072_fresh_089 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy082 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv)
      0

theorem nb072_fresh_090 (x : Var) (H : Class) :
    (nb072AlphaDummy081 x H) ∉
      (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy072 x H))).fv) :=
  by
  simpa only [nb072AlphaDummy081] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy072 x H))).fv)
      0

theorem nb072_fresh_091 (x : Var) (H : Class) :
    (nb072AlphaDummy077 x H) ∉
      (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy073 x H))).fv) :=
  by
  simpa only [nb072AlphaDummy077] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy073 x H))).fv)
      0

theorem nb072_fresh_092 (x : Var) (H : Class) :
    (nb072AlphaDummy083 x H) ∉
      (((Class.cv (nb072AlphaDummy073 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy073 x H))).fv) :=
  by
  simpa only [nb072AlphaDummy083] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy073 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy073 x H))).fv)
      0

theorem nb072_fresh_093 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy098 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy098] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) 0

theorem nb072_fresh_094 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy099 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy099] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) 1

theorem nb072_fresh_095 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy100 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy100] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) 2

theorem nb072_distinct_096 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy098 A B R S_cls H) ≠ (nb072AlphaDummy099 A B R S_cls H) := by
  simpa only [nb072AlphaDummy098, nb072AlphaDummy099] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_distinct_097 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy098 A B R S_cls H) ≠ (nb072AlphaDummy100 A B R S_cls H) := by
  simpa only [nb072AlphaDummy098, nb072AlphaDummy100] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb072_distinct_098 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy100 A B R S_cls H) := by
  simpa only [nb072AlphaDummy099, nb072AlphaDummy100] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb072_fresh_099 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy101 x y H) ∉
      (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy101] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) 0

theorem nb072_fresh_100 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy102 x y H) ∉
      (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy102] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) 1

theorem nb072_fresh_101 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy103 x y H) ∉
      (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy103] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) 2

theorem nb072_distinct_102 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy101 x y H) ≠ (nb072AlphaDummy102 x y H) := by
  simpa only [nb072AlphaDummy101, nb072AlphaDummy102] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_distinct_103 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy101 x y H) ≠ (nb072AlphaDummy103 x y H) := by
  simpa only [nb072AlphaDummy101, nb072AlphaDummy103] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb072_distinct_104 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy103 x y H) := by
  simpa only [nb072AlphaDummy102, nb072AlphaDummy103] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb072_fresh_105 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy110 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy110] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv)
      0

theorem nb072_fresh_106 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy106 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy106] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv)
      0

theorem nb072_fresh_107 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy112 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy112] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv)
      0

theorem nb072_fresh_108 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy111 x y H) ∉
      (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy102 x y H))).fv) :=
  by
  simpa only [nb072AlphaDummy111] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy102 x y H))).fv)
      0

theorem nb072_fresh_109 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy107 x y H) ∉
      (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy103 x y H))).fv) :=
  by
  simpa only [nb072AlphaDummy107] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy103 x y H))).fv)
      0

theorem nb072_fresh_110 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy113 x y H) ∉
      (((Class.cv (nb072AlphaDummy103 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy103 x y H))).fv) :=
  by
  simpa only [nb072AlphaDummy113] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy103 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy103 x y H))).fv)
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
    (nb072AlphaDummy160 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy118 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy160] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy118 A B R S_cls H))).fv) 0

theorem nb072_fresh_112 (y : Var) (H : Class) :
    (nb072AlphaDummy161 y H) ∉ (((Class.cv (nb072AlphaDummy119 y H))).fv) := by
  simpa only [nb072AlphaDummy161] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy119 y H))).fv) 0

theorem nb072_fresh_113 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy132 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy132] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) 0

theorem nb072_fresh_114 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy133 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy133] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) 1

theorem nb072_distinct_115 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy132 A B R S_cls H) ≠ (nb072AlphaDummy133 A B R S_cls H) := by
  simpa only [nb072AlphaDummy132, nb072AlphaDummy133] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_fresh_116 (y : Var) (H : Class) :
    (nb072AlphaDummy134 y H) ∉ (((Class.cv (nb072AlphaDummy127 y H))).fv) := by
  simpa only [nb072AlphaDummy134] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy127 y H))).fv) 0

theorem nb072_fresh_117 (y : Var) (H : Class) :
    (nb072AlphaDummy135 y H) ∉ (((Class.cv (nb072AlphaDummy127 y H))).fv) := by
  simpa only [nb072AlphaDummy135] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy127 y H))).fv) 1

theorem nb072_distinct_118 (y : Var) (H : Class) :
    (nb072AlphaDummy134 y H) ≠ (nb072AlphaDummy135 y H) := by
  simpa only [nb072AlphaDummy134, nb072AlphaDummy135] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy127 y H))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_119 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy138 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy138] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) 0

theorem nb072_fresh_120 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy139 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy139] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) 1

theorem nb072_fresh_121 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy140 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy140] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) 2

theorem nb072_distinct_122 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy138 A B R S_cls H) ≠ (nb072AlphaDummy139 A B R S_cls H) := by
  simpa only [nb072AlphaDummy138, nb072AlphaDummy139] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb072_distinct_123 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy138 A B R S_cls H) ≠ (nb072AlphaDummy140 A B R S_cls H) := by
  simpa only [nb072AlphaDummy138, nb072AlphaDummy140] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb072_distinct_124 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy140 A B R S_cls H) := by
  simpa only [nb072AlphaDummy139, nb072AlphaDummy140] using
    (freshVar_injective
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb072_fresh_125 (y : Var) (H : Class) :
    (nb072AlphaDummy141 y H) ∉
      (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy141] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) 0

theorem nb072_fresh_126 (y : Var) (H : Class) :
    (nb072AlphaDummy142 y H) ∉
      (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy142] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) 1

theorem nb072_fresh_127 (y : Var) (H : Class) :
    (nb072AlphaDummy143 y H) ∉
      (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb072AlphaDummy143] using
    freshVar_not_mem (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) 2

theorem nb072_distinct_128 (y : Var) (H : Class) :
    (nb072AlphaDummy141 y H) ≠ (nb072AlphaDummy142 y H) := by
  simpa only [nb072AlphaDummy141, nb072AlphaDummy142] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_distinct_129 (y : Var) (H : Class) :
    (nb072AlphaDummy141 y H) ≠ (nb072AlphaDummy143 y H) := by
  simpa only [nb072AlphaDummy141, nb072AlphaDummy143] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb072_distinct_130 (y : Var) (H : Class) :
    (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy143 y H) := by
  simpa only [nb072AlphaDummy142, nb072AlphaDummy143] using
    (freshVar_injective (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb072_fresh_131 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy150 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy150] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv)
      0

theorem nb072_fresh_132 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy146 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy146] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv)
      0

theorem nb072_fresh_133 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy152 A B R S_cls H) ∉
      (((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy152] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv)
      0

theorem nb072_fresh_134 (y : Var) (H : Class) :
    (nb072AlphaDummy151 y H) ∉
      (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy142 y H))).fv) :=
  by
  simpa only [nb072AlphaDummy151] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy142 y H))).fv)
      0

theorem nb072_fresh_135 (y : Var) (H : Class) :
    (nb072AlphaDummy147 y H) ∉
      (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy143 y H))).fv) :=
  by
  simpa only [nb072AlphaDummy147] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy143 y H))).fv)
      0

theorem nb072_fresh_136 (y : Var) (H : Class) :
    (nb072AlphaDummy153 y H) ∉
      (((Class.cv (nb072AlphaDummy143 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy143 y H))).fv) :=
  by
  simpa only [nb072AlphaDummy153] using
    freshVar_not_mem
      (((Class.cv (nb072AlphaDummy143 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy143 y H))).fv)
      0

theorem nb072_fresh_137 (x : Var) (H : Class) :
    (nb072AlphaDummy056 x H) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv) :=
  by
  simpa only [nb072AlphaDummy056] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv) 0

theorem nb072_fresh_138 (x : Var) (H : Class) :
    (nb072AlphaDummy057 x H) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv) :=
  by
  simpa only [nb072AlphaDummy057] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv) 1

theorem nb072_distinct_139 (x : Var) (H : Class) :
    (nb072AlphaDummy056 x H) ≠ (nb072AlphaDummy057 x H) := by
  simpa only [nb072AlphaDummy056, nb072AlphaDummy057] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_140 (x : Var) (y : Var) :
    (nb072AlphaDummy004 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072AlphaDummy004] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb072_fresh_141 (x : Var) (y : Var) :
    (nb072AlphaDummy005 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072AlphaDummy005] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb072_distinct_142 (x : Var) (y : Var) :
    (nb072AlphaDummy004 x y) ≠ (nb072AlphaDummy005 x y) := by
  simpa only [nb072AlphaDummy004, nb072AlphaDummy005] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_143 (y : Var) (H : Class) :
    (nb072AlphaDummy126 y H) ∉
      (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv) :=
  by
  simpa only [nb072AlphaDummy126] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv) 0

theorem nb072_fresh_144 (y : Var) (H : Class) :
    (nb072AlphaDummy127 y H) ∉
      (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv) :=
  by
  simpa only [nb072AlphaDummy127] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv) 1

theorem nb072_distinct_145 (y : Var) (H : Class) :
    (nb072AlphaDummy126 y H) ≠ (nb072AlphaDummy127 y H) := by
  simpa only [nb072AlphaDummy126, nb072AlphaDummy127] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_146 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy014 A B R S_cls H) ∉
      (((Wff.classMem (Class.cv (nb072AlphaDummy010 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy010 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy014] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072AlphaDummy010 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy010 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv)
      0

theorem nb072_fresh_147 (x : Var) (y : Var) :
    (nb072AlphaDummy015 x y) ∉
      (((Wff.classMem (Class.cv (nb072AlphaDummy012 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy012 x y)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy012 x y))).fv) :=
  by
  simpa only [nb072AlphaDummy015] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072AlphaDummy012 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy012 x y)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy012 x y))).fv)
      0

theorem nb072_fresh_148 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy066 A B R S_cls H) ∉
      (((Wff.classMem (Class.cv (nb072AlphaDummy062 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy062 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy066] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072AlphaDummy062 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy062 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv)
      0

theorem nb072_fresh_149 (x : Var) (H : Class) :
    (nb072AlphaDummy067 x H) ∉
      (((Wff.classMem (Class.cv (nb072AlphaDummy064 x H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy064 x H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy064 x H))).fv) :=
  by
  simpa only [nb072AlphaDummy067] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072AlphaDummy064 x H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy064 x H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy064 x H))).fv)
      0

theorem nb072_fresh_150 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy096 A B R S_cls H) ∉
      (((Wff.classMem (Class.cv (nb072AlphaDummy092 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy092 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy096] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072AlphaDummy092 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy092 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv)
      0

theorem nb072_fresh_151 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy097 x y H) ∉
      (((Wff.classMem (Class.cv (nb072AlphaDummy094 x y H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy094 x y H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy094 x y H))).fv) :=
  by
  simpa only [nb072AlphaDummy097] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072AlphaDummy094 x y H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy094 x y H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy094 x y H))).fv)
      0

theorem nb072_fresh_152 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy136 A B R S_cls H) ∉
      (((Wff.classMem (Class.cv (nb072AlphaDummy132 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy132 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy136] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072AlphaDummy132 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy132 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv)
      0

theorem nb072_fresh_153 (y : Var) (H : Class) :
    (nb072AlphaDummy137 y H) ∉
      (((Wff.classMem (Class.cv (nb072AlphaDummy134 y H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy134 y H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy134 y H))).fv) :=
  by
  simpa only [nb072AlphaDummy137] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb072AlphaDummy134 y H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy134 y H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy134 y H))).fv)
      0

theorem nb072_fresh_154 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy006 A B R S_cls H) ∉
      (((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb072AlphaDummy006] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb072_fresh_155 (x : Var) (y : Var) :
    (nb072AlphaDummy007 x y) ∉
      (((synCcompl (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCphi (Class.cv (nb072AlphaDummy005 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb072AlphaDummy007] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCphi (Class.cv (nb072AlphaDummy005 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb072_fresh_156 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy042 A B R S_cls H) ∉
      (((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb072AlphaDummy042] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb072_fresh_157 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy043 x y H) ∉
      (((synCcompl (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCphi (Class.cv (nb072AlphaDummy041 x y H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb072AlphaDummy043] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCphi (Class.cv (nb072AlphaDummy041 x y H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb072_fresh_158 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy058 A B R S_cls H) ∉
      (((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb072AlphaDummy058] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb072_fresh_159 (x : Var) (H : Class) :
    (nb072AlphaDummy059 x H) ∉
      (((synCcompl (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCphi (Class.cv (nb072AlphaDummy057 x H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb072AlphaDummy059] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCphi (Class.cv (nb072AlphaDummy057 x H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb072_fresh_160 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy128 A B R S_cls H) ∉
      (((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb072AlphaDummy128] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb072_fresh_161 (y : Var) (H : Class) :
    (nb072AlphaDummy129 y H) ∉
      (((synCcompl (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCphi (Class.cv (nb072AlphaDummy127 y H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb072AlphaDummy129] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCphi (Class.cv (nb072AlphaDummy127 y H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb072_fresh_162 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy026 A B R S_cls H) ∉
      (((synCcompl (Class.cv (nb072AlphaDummy017 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy026] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb072AlphaDummy017 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_163 (x : Var) (y : Var) :
    (nb072AlphaDummy027 x y) ∉
      (((synCcompl (Class.cv (nb072AlphaDummy020 x y)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy021 x y)))).fv) :=
  by
  simpa only [nb072AlphaDummy027] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb072AlphaDummy020 x y)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy021 x y)))).fv)
      0

theorem nb072_fresh_164 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy078 A B R S_cls H) ∉
      (((synCcompl (Class.cv (nb072AlphaDummy069 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy078] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb072AlphaDummy069 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_165 (x : Var) (H : Class) :
    (nb072AlphaDummy079 x H) ∉
      (((synCcompl (Class.cv (nb072AlphaDummy072 x H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy073 x H)))).fv) :=
  by
  simpa only [nb072AlphaDummy079] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb072AlphaDummy072 x H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy073 x H)))).fv)
      0

theorem nb072_fresh_166 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy108 A B R S_cls H) ∉
      (((synCcompl (Class.cv (nb072AlphaDummy099 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy108] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb072AlphaDummy099 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_167 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy109 x y H) ∉
      (((synCcompl (Class.cv (nb072AlphaDummy102 x y H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy103 x y H)))).fv) :=
  by
  simpa only [nb072AlphaDummy109] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb072AlphaDummy102 x y H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy103 x y H)))).fv)
      0

theorem nb072_fresh_168 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy148 A B R S_cls H) ∉
      (((synCcompl (Class.cv (nb072AlphaDummy139 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy148] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb072AlphaDummy139 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_169 (y : Var) (H : Class) :
    (nb072AlphaDummy149 y H) ∉
      (((synCcompl (Class.cv (nb072AlphaDummy142 y H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy143 y H)))).fv) :=
  by
  simpa only [nb072AlphaDummy149] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb072AlphaDummy142 y H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy143 y H)))).fv)
      0

theorem nb072_fresh_170 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy034 A B R S_cls H) ∉
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb072AlphaDummy034] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb072_fresh_171 (x : Var) (y : Var) :
    (nb072AlphaDummy035 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy005 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb072AlphaDummy035] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy005 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb072_fresh_172 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy162 A B R S_cls H) ∉
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb072AlphaDummy162] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb072_fresh_173 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy163 x y H) ∉
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy041 x y H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb072AlphaDummy163] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy041 x y H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb072_fresh_174 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy086 A B R S_cls H) ∉
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb072AlphaDummy086] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb072_fresh_175 (x : Var) (H : Class) :
    (nb072AlphaDummy087 x H) ∉
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy057 x H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb072AlphaDummy087] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy057 x H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb072_fresh_176 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy156 A B R S_cls H) ∉
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb072AlphaDummy156] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb072_fresh_177 (y : Var) (H : Class) :
    (nb072AlphaDummy157 y H) ∉
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy127 y H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb072AlphaDummy157] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy127 y H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb072_fresh_178 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy038 A B R S_cls H) ∉
      (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
        ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy038] using
    freshVar_not_mem
      (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
        ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_179 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy039 A B R S_cls H) ∉
      (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
        ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy039] using
    freshVar_not_mem
      (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
        ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv)
      1

theorem nb072_distinct_180 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy038 A B R S_cls H) ≠ (nb072AlphaDummy039 A B R S_cls H) := by
  simpa only [nb072AlphaDummy038, nb072AlphaDummy039] using
    (freshVar_injective (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
        ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_181 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy040 x y H) ∉
      (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) :=
  by
  simpa only [nb072AlphaDummy040] using
    freshVar_not_mem (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) 0

theorem nb072_fresh_182 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy041 x y H) ∉
      (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) :=
  by
  simpa only [nb072AlphaDummy041] using
    freshVar_not_mem (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) 1

theorem nb072_distinct_183 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy040 x y H) ≠ (nb072AlphaDummy041 x y H) := by
  simpa only [nb072AlphaDummy040, nb072AlphaDummy041] using
    (freshVar_injective (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb072_fresh_184 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy022 A B R S_cls H) ∉
      (((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
            (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
            (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy022] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
            (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
            (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_185 (x : Var) (y : Var) :
    (nb072AlphaDummy023 x y) ∉
      (((synCnin (Class.cv (nb072AlphaDummy020 x y))
            (Class.cv (nb072AlphaDummy021 x y)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy020 x y))
            (Class.cv (nb072AlphaDummy021 x y)))).fv) :=
  by
  simpa only [nb072AlphaDummy023] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb072AlphaDummy020 x y))
            (Class.cv (nb072AlphaDummy021 x y)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy020 x y))
            (Class.cv (nb072AlphaDummy021 x y)))).fv)
      0

theorem nb072_fresh_186 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy074 A B R S_cls H) ∉
      (((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
            (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
            (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy074] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
            (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
            (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_187 (x : Var) (H : Class) :
    (nb072AlphaDummy075 x H) ∉
      (((synCnin (Class.cv (nb072AlphaDummy072 x H))
            (Class.cv (nb072AlphaDummy073 x H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy072 x H))
            (Class.cv (nb072AlphaDummy073 x H)))).fv) :=
  by
  simpa only [nb072AlphaDummy075] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb072AlphaDummy072 x H))
            (Class.cv (nb072AlphaDummy073 x H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy072 x H))
            (Class.cv (nb072AlphaDummy073 x H)))).fv)
      0

theorem nb072_fresh_188 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy104 A B R S_cls H) ∉
      (((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
            (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
            (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy104] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
            (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
            (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_189 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy105 x y H) ∉
      (((synCnin (Class.cv (nb072AlphaDummy102 x y H))
            (Class.cv (nb072AlphaDummy103 x y H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy102 x y H))
            (Class.cv (nb072AlphaDummy103 x y H)))).fv) :=
  by
  simpa only [nb072AlphaDummy105] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb072AlphaDummy102 x y H))
            (Class.cv (nb072AlphaDummy103 x y H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy102 x y H))
            (Class.cv (nb072AlphaDummy103 x y H)))).fv)
      0

theorem nb072_fresh_190 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy144 A B R S_cls H) ∉
      (((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
            (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
            (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy144] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
            (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
            (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_191 (y : Var) (H : Class) :
    (nb072AlphaDummy145 y H) ∉
      (((synCnin (Class.cv (nb072AlphaDummy142 y H))
            (Class.cv (nb072AlphaDummy143 y H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy142 y H))
            (Class.cv (nb072AlphaDummy143 y H)))).fv) :=
  by
  simpa only [nb072AlphaDummy145] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb072AlphaDummy142 y H))
            (Class.cv (nb072AlphaDummy143 y H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy142 y H))
            (Class.cv (nb072AlphaDummy143 y H)))).fv)
      0

theorem nb072_fresh_192 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy036 A B R S_cls H) ∉
      (((synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy036] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_193 (x : Var) (y : Var) :
    (nb072AlphaDummy037 x y) ∉
      (((synCphi (Class.cv (nb072AlphaDummy005 x y)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy005 x y)))).fv) :=
  by
  simpa only [nb072AlphaDummy037] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb072AlphaDummy005 x y)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy005 x y)))).fv)
      0

theorem nb072_fresh_194 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy164 A B R S_cls H) ∉
      (((synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy164] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_195 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy165 x y H) ∉
      (((synCphi (Class.cv (nb072AlphaDummy041 x y H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy041 x y H)))).fv) :=
  by
  simpa only [nb072AlphaDummy165] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb072AlphaDummy041 x y H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy041 x y H)))).fv)
      0

theorem nb072_fresh_196 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy088 A B R S_cls H) ∉
      (((synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy088] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_197 (x : Var) (H : Class) :
    (nb072AlphaDummy089 x H) ∉
      (((synCphi (Class.cv (nb072AlphaDummy057 x H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy057 x H)))).fv) :=
  by
  simpa only [nb072AlphaDummy089] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb072AlphaDummy057 x H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy057 x H)))).fv)
      0

theorem nb072_fresh_198 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy158 A B R S_cls H) ∉
      (((synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy158] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_199 (y : Var) (H : Class) :
    (nb072AlphaDummy159 y H) ∉
      (((synCphi (Class.cv (nb072AlphaDummy127 y H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy127 y H)))).fv) :=
  by
  simpa only [nb072AlphaDummy159] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb072AlphaDummy127 y H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy127 y H)))).fv)
      0

theorem nb072_fresh_200 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy046 A B R S_cls H) ∉
      ((H).fv ∪ ((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy046] using
    freshVar_not_mem ((H).fv ∪ ((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv) 0

theorem nb072_fresh_201 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy116 A B R S_cls H) ∉
      ((H).fv ∪ ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) :=
  by
  simpa only [nb072AlphaDummy116] using
    freshVar_not_mem ((H).fv ∪ ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) 0

theorem nb072_fresh_202 (x : Var) (H : Class) :
    (nb072AlphaDummy047 x H) ∉ ((H).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb072AlphaDummy047] using freshVar_not_mem ((H).fv ∪ ((Class.cv x)).fv) 0

theorem nb072_fresh_203 (y : Var) (H : Class) :
    (nb072AlphaDummy117 y H) ∉ ((H).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072AlphaDummy117] using freshVar_not_mem ((H).fv ∪ ((Class.cv y)).fv) 0

theorem nb072_fresh_204 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∉
      ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) :=
  by
  simpa only [nb072AlphaDummy000] using
    freshVar_not_mem ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb072_fresh_205 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∉
      ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) :=
  by
  simpa only [nb072AlphaDummy001] using
    freshVar_not_mem ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1

theorem nb072_distinct_206 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy001 A B R S_cls H) := by
  simpa only [nb072AlphaDummy000, nb072AlphaDummy001] using
    (freshVar_injective ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (i := 0) (j := 1)
      (by decide))

theorem nb072_fresh_207 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy048 A B R S_cls H) ∉
      (({(nb072AlphaDummy046 A B R S_cls H)} : Finset Var) ∪
        ((synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy046 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy048] using
    freshVar_not_mem
      (({(nb072AlphaDummy046 A B R S_cls H)} : Finset Var) ∪
        ((synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy046 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_208 (x : Var) (H : Class) :
    (nb072AlphaDummy049 x H) ∉
      (({(nb072AlphaDummy047 x H)} : Finset Var) ∪
        ((synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H)))).fv) :=
  by
  simpa only [nb072AlphaDummy049] using
    freshVar_not_mem
      (({(nb072AlphaDummy047 x H)} : Finset Var) ∪
        ((synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H)))).fv)
      0

theorem nb072_fresh_209 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) :
    (nb072AlphaDummy118 A B R S_cls H) ∉
      (({(nb072AlphaDummy116 A B R S_cls H)} : Finset Var) ∪
        ((synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy116 A B R S_cls H)))).fv) :=
  by
  simpa only [nb072AlphaDummy118] using
    freshVar_not_mem
      (({(nb072AlphaDummy116 A B R S_cls H)} : Finset Var) ∪
        ((synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy116 A B R S_cls H)))).fv)
      0

theorem nb072_fresh_210 (y : Var) (H : Class) :
    (nb072AlphaDummy119 y H) ∉
      (({(nb072AlphaDummy117 y H)} : Finset Var) ∪
        ((synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H)))).fv) :=
  by
  simpa only [nb072AlphaDummy119] using
    freshVar_not_mem
      (({(nb072AlphaDummy117 y H)} : Finset Var) ∪
        ((synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H)))).fv)
      0

theorem nb072_support_mem_0000 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0001 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy002 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy003 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy003;
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
      (((synCcompl (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCphi (Class.cv (nb072AlphaDummy005 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072AlphaDummy004 x y) from (by
          unfold nb072AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072AlphaDummy005 x y) from (by
            unfold nb072AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0004 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy002 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy003 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy003;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0005 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCphi (Class.cv (nb072AlphaDummy005 x y))))))).fv ∪
        ((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCphi (Class.cv (nb072AlphaDummy005 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072AlphaDummy004 x y) from (by
          unfold nb072AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072AlphaDummy005 x y) from (by
            unfold nb072AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0006 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy003 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0007 (x : Var) (y : Var) :
    (nb072AlphaDummy005 x y) ∈ (((Class.cv (nb072AlphaDummy005 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0008 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy010 A B R S_cls H) ∈
      (((Wff.classMem (Class.cv (nb072AlphaDummy010 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy010 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv) :=
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
    (nb072AlphaDummy012 x y) ∈
      (((Wff.classMem (Class.cv (nb072AlphaDummy012 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy012 x y)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy012 x y))).fv) :=
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
    (nb072AlphaDummy010 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0011 (x : Var) (y : Var) :
    (nb072AlphaDummy012 x y) ∈
      (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0012 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy017 A B R S_cls H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
            (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
            (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0013 (x : Var) (y : Var) :
    (nb072AlphaDummy020 x y) ∈
      (((synCnin (Class.cv (nb072AlphaDummy020 x y))
            (Class.cv (nb072AlphaDummy021 x y)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy020 x y))
            (Class.cv (nb072AlphaDummy021 x y)))).fv) :=
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
    (nb072AlphaDummy017 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0015 (x : Var) (y : Var) :
    (nb072AlphaDummy020 x y) ∈
      (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy021 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0016 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy018 A B R S_cls H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
            (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy017 A B R S_cls H))
            (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0017 (x : Var) (y : Var) :
    (nb072AlphaDummy021 x y) ∈
      (((synCnin (Class.cv (nb072AlphaDummy020 x y))
            (Class.cv (nb072AlphaDummy021 x y)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy020 x y))
            (Class.cv (nb072AlphaDummy021 x y)))).fv) :=
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
    (nb072AlphaDummy018 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0019 (x : Var) (y : Var) :
    (nb072AlphaDummy021 x y) ∈
      (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy021 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0020 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy017 A B R S_cls H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy017 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0021 (x : Var) (y : Var) :
    (nb072AlphaDummy020 x y) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy020 x y)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy021 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0022 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy017 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy017 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0023 (x : Var) (y : Var) :
    (nb072AlphaDummy020 x y) ∈
      (((Class.cv (nb072AlphaDummy020 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy020 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0024 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy018 A B R S_cls H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy017 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy018 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0025 (x : Var) (y : Var) :
    (nb072AlphaDummy021 x y) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy020 x y)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy021 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0026 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy018 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy018 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0027 (x : Var) (y : Var) :
    (nb072AlphaDummy021 x y) ∈
      (((Class.cv (nb072AlphaDummy021 x y))).fv ∪
        ((Class.cv (nb072AlphaDummy021 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0028 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) :=
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
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy002 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy003 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy003;
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
      (((synCcompl (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCphi (Class.cv (nb072AlphaDummy005 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072AlphaDummy004 x y) from (by
          unfold nb072AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072AlphaDummy005 x y) from (by
            unfold nb072AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0032 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy002 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy003 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy003;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0033 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072AlphaDummy004 x y) from (by
          unfold nb072AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072AlphaDummy005 x y) from (by
            unfold nb072AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0034 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy003 A B R S_cls H) ∈
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0035 (x : Var) (y : Var) :
    (nb072AlphaDummy005 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy005 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0036 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy003 A B R S_cls H) ∈
      (((synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0037 (x : Var) (y : Var) :
    (nb072AlphaDummy005 x y) ∈
      (((synCphi (Class.cv (nb072AlphaDummy005 x y)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy005 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0038 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
        ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv) :=
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
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy038 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy039 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy039;
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
    x ∈ (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) :=
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
      (((synCcompl (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCphi (Class.cv (nb072AlphaDummy041 x y H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072AlphaDummy040 x y H) from (by
          unfold nb072AlphaDummy040;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072AlphaDummy041 x y H) from (by
            unfold nb072AlphaDummy041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0042 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy038 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy039 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy039;
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
      (((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072AlphaDummy040 x y H) from (by
          unfold nb072AlphaDummy040;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072AlphaDummy041 x y H) from (by
            unfold nb072AlphaDummy041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0044 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      ((H).fv ∪ ((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0045 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (({(nb072AlphaDummy046 A B R S_cls H)} : Finset Var) ∪
        ((synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy046 A B R S_cls H)))).fv) :=
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
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy046 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy048 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy048;
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
        (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy046 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy046;
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
      (({(nb072AlphaDummy047 x H)} : Finset Var) ∪
        ((synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H)))).fv) :=
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
      (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
            (Class.cab (nb072AlphaDummy047 x H)
              (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
            (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072AlphaDummy049 x H) from (by
          unfold nb072AlphaDummy049;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0048 x H) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072AlphaDummy047 x H) from (by
            unfold nb072AlphaDummy047;
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
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0051 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy054 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy055 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy055;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0052 (x : Var) (H : Class) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0053 (x : Var) (H : Class) :
    x ∈
      (((synCcompl (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCphi (Class.cv (nb072AlphaDummy057 x H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072AlphaDummy056 x H) from (by
          unfold nb072AlphaDummy056;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072AlphaDummy057 x H) from (by
            unfold nb072AlphaDummy057;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0054 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy000 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy054 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy055 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy055;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0055 (x : Var) (H : Class) :
    x ∈
      (((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCphi (Class.cv (nb072AlphaDummy057 x H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCphi (Class.cv (nb072AlphaDummy057 x H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb072AlphaDummy056 x H) from (by
          unfold nb072AlphaDummy056;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb072AlphaDummy057 x H) from (by
            unfold nb072AlphaDummy057;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0056 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy055 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0057 (x : Var) (H : Class) :
    (nb072AlphaDummy057 x H) ∈ (((Class.cv (nb072AlphaDummy057 x H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0058 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy062 A B R S_cls H) ∈
      (((Wff.classMem (Class.cv (nb072AlphaDummy062 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy062 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv) :=
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
    (nb072AlphaDummy064 x H) ∈
      (((Wff.classMem (Class.cv (nb072AlphaDummy064 x H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy064 x H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy064 x H))).fv) :=
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
    (nb072AlphaDummy062 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0061 (x : Var) (H : Class) :
    (nb072AlphaDummy064 x H) ∈
      (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0062 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy069 A B R S_cls H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
            (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
            (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0063 (x : Var) (H : Class) :
    (nb072AlphaDummy072 x H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy072 x H))
            (Class.cv (nb072AlphaDummy073 x H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy072 x H))
            (Class.cv (nb072AlphaDummy073 x H)))).fv) :=
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
    (nb072AlphaDummy069 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0065 (x : Var) (H : Class) :
    (nb072AlphaDummy072 x H) ∈
      (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy073 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0066 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy070 A B R S_cls H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
            (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy069 A B R S_cls H))
            (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0067 (x : Var) (H : Class) :
    (nb072AlphaDummy073 x H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy072 x H))
            (Class.cv (nb072AlphaDummy073 x H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy072 x H))
            (Class.cv (nb072AlphaDummy073 x H)))).fv) :=
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
    (nb072AlphaDummy070 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0069 (x : Var) (H : Class) :
    (nb072AlphaDummy073 x H) ∈
      (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy073 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0070 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy069 A B R S_cls H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy069 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0071 (x : Var) (H : Class) :
    (nb072AlphaDummy072 x H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy072 x H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy073 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0072 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy069 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy069 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0073 (x : Var) (H : Class) :
    (nb072AlphaDummy072 x H) ∈
      (((Class.cv (nb072AlphaDummy072 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy072 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0074 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy070 A B R S_cls H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy069 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy070 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0075 (x : Var) (H : Class) :
    (nb072AlphaDummy073 x H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy072 x H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy073 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0076 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy070 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy070 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0077 (x : Var) (H : Class) :
    (nb072AlphaDummy073 x H) ∈
      (((Class.cv (nb072AlphaDummy073 x H))).fv ∪
        ((Class.cv (nb072AlphaDummy073 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0078 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy046 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0079 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy046 A B R S_cls H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy046 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy046 A B R S_cls H) ≠ (nb072AlphaDummy054 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy046 A B R S_cls H) ≠ (nb072AlphaDummy055 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy055;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0080 (x : Var) (H : Class) :
    (nb072AlphaDummy047 x H) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0081 (x : Var) (H : Class) :
    (nb072AlphaDummy047 x H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCphi (Class.cv (nb072AlphaDummy057 x H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy056 x H) from (by
          unfold nb072AlphaDummy056;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy057 x H) from (by
            unfold nb072AlphaDummy057;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0082 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy046 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy046 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy046 A B R S_cls H) ≠ (nb072AlphaDummy054 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy046 A B R S_cls H) ≠ (nb072AlphaDummy055 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy055;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0083 (x : Var) (H : Class) :
    (nb072AlphaDummy047 x H) ∈
      (((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv (nb072AlphaDummy047 x H))
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy057 x H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy056 x H) from (by
          unfold nb072AlphaDummy056;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy057 x H) from (by
            unfold nb072AlphaDummy057;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0084 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy055 A B R S_cls H) ∈
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0085 (x : Var) (H : Class) :
    (nb072AlphaDummy057 x H) ∈
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy057 x H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0086 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy055 A B R S_cls H) ∈
      (((synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0087 (x : Var) (H : Class) :
    (nb072AlphaDummy057 x H) ∈
      (((synCphi (Class.cv (nb072AlphaDummy057 x H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy057 x H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0088 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy048 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy048 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0089 (x : Var) (H : Class) :
    (nb072AlphaDummy049 x H) ∈ (((Class.cv (nb072AlphaDummy049 x H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0090 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy039 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0091 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy041 x y H) ∈ (((Class.cv (nb072AlphaDummy041 x y H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0092 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy092 A B R S_cls H) ∈
      (((Wff.classMem (Class.cv (nb072AlphaDummy092 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy092 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv) :=
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
    (nb072AlphaDummy094 x y H) ∈
      (((Wff.classMem (Class.cv (nb072AlphaDummy094 x y H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy094 x y H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy094 x y H))).fv) :=
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
    (nb072AlphaDummy092 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0095 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy094 x y H) ∈
      (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0096 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy099 A B R S_cls H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
            (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
            (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0097 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy102 x y H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy102 x y H))
            (Class.cv (nb072AlphaDummy103 x y H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy102 x y H))
            (Class.cv (nb072AlphaDummy103 x y H)))).fv) :=
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
    (nb072AlphaDummy099 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0099 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy102 x y H) ∈
      (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy103 x y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0100 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy100 A B R S_cls H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
            (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy099 A B R S_cls H))
            (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0101 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy103 x y H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy102 x y H))
            (Class.cv (nb072AlphaDummy103 x y H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy102 x y H))
            (Class.cv (nb072AlphaDummy103 x y H)))).fv) :=
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
    (nb072AlphaDummy100 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0103 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy103 x y H) ∈
      (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy103 x y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0104 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy099 A B R S_cls H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy099 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0105 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy102 x y H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy102 x y H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy103 x y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0106 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy099 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy099 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0107 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy102 x y H) ∈
      (((Class.cv (nb072AlphaDummy102 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy102 x y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0108 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy100 A B R S_cls H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy099 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy100 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0109 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy103 x y H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy102 x y H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy103 x y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0110 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy100 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy100 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0111 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy103 x y H) ∈
      (((Class.cv (nb072AlphaDummy103 x y H))).fv ∪
        ((Class.cv (nb072AlphaDummy103 x y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0112 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
        ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv) :=
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
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy038 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy039 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy039;
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
    y ∈ (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) :=
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
      (((synCcompl (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCphi (Class.cv (nb072AlphaDummy041 x y H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072AlphaDummy040 x y H) from (by
          unfold nb072AlphaDummy040;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072AlphaDummy041 x y H) from (by
            unfold nb072AlphaDummy041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0116 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy038 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy039 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy039;
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
      (((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072AlphaDummy040 x y H) from (by
          unfold nb072AlphaDummy040;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072AlphaDummy041 x y H) from (by
            unfold nb072AlphaDummy041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0118 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∈
      ((H).fv ∪ ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0119 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (({(nb072AlphaDummy116 A B R S_cls H)} : Finset Var) ∪
        ((synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy116 A B R S_cls H)))).fv) :=
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
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
            (Class.cab (nb072AlphaDummy116 A B R S_cls H)
              (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
            (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy118 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy118;
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
        (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy116 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy116;
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
      (({(nb072AlphaDummy117 y H)} : Finset Var) ∪
        ((synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H)))).fv) :=
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
      (((Class.cab (nb072AlphaDummy119 y H) (Wff.classEq
            (Class.cab (nb072AlphaDummy117 y H)
              (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
            (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072AlphaDummy119 y H) from (by
          unfold nb072AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0122 y H) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072AlphaDummy117 y H) from (by
            unfold nb072AlphaDummy117;
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
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0125 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy124 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy125 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy125;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0126 (y : Var) (H : Class) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0127 (y : Var) (H : Class) :
    y ∈
      (((synCcompl (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCphi (Class.cv (nb072AlphaDummy127 y H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072AlphaDummy126 y H) from (by
          unfold nb072AlphaDummy126;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072AlphaDummy127 y H) from (by
            unfold nb072AlphaDummy127;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0128 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy001 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy124 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy125 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy125;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0129 (y : Var) (H : Class) :
    y ∈
      (((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCphi (Class.cv (nb072AlphaDummy127 y H))))))).fv ∪
        ((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCphi (Class.cv (nb072AlphaDummy127 y H))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb072AlphaDummy126 y H) from (by
          unfold nb072AlphaDummy126;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb072AlphaDummy127 y H) from (by
            unfold nb072AlphaDummy127;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0130 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy125 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0131 (y : Var) (H : Class) :
    (nb072AlphaDummy127 y H) ∈ (((Class.cv (nb072AlphaDummy127 y H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0132 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy132 A B R S_cls H) ∈
      (((Wff.classMem (Class.cv (nb072AlphaDummy132 A B R S_cls H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy132 A B R S_cls H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv) :=
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
    (nb072AlphaDummy134 y H) ∈
      (((Wff.classMem (Class.cv (nb072AlphaDummy134 y H)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb072AlphaDummy134 y H)) (synC1c))).fv ∪
        ((Class.cv (nb072AlphaDummy134 y H))).fv) :=
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
    (nb072AlphaDummy132 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0135 (y : Var) (H : Class) :
    (nb072AlphaDummy134 y H) ∈
      (((Class.cv (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0136 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy139 A B R S_cls H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
            (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
            (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0137 (y : Var) (H : Class) :
    (nb072AlphaDummy142 y H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy142 y H))
            (Class.cv (nb072AlphaDummy143 y H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy142 y H))
            (Class.cv (nb072AlphaDummy143 y H)))).fv) :=
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
    (nb072AlphaDummy139 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0139 (y : Var) (H : Class) :
    (nb072AlphaDummy142 y H) ∈
      (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy143 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0140 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy140 A B R S_cls H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
            (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy139 A B R S_cls H))
            (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0141 (y : Var) (H : Class) :
    (nb072AlphaDummy143 y H) ∈
      (((synCnin (Class.cv (nb072AlphaDummy142 y H))
            (Class.cv (nb072AlphaDummy143 y H)))).fv ∪
        ((synCnin (Class.cv (nb072AlphaDummy142 y H))
            (Class.cv (nb072AlphaDummy143 y H)))).fv) :=
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
    (nb072AlphaDummy140 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0143 (y : Var) (H : Class) :
    (nb072AlphaDummy143 y H) ∈
      (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy143 y H))).fv) :=
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
    (nb072AlphaDummy139 A B R S_cls H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy139 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0145 (y : Var) (H : Class) :
    (nb072AlphaDummy142 y H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy142 y H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy143 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0146 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy139 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy139 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0147 (y : Var) (H : Class) :
    (nb072AlphaDummy142 y H) ∈
      (((Class.cv (nb072AlphaDummy142 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy142 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0148 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy140 A B R S_cls H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy139 A B R S_cls H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy140 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0149 (y : Var) (H : Class) :
    (nb072AlphaDummy143 y H) ∈
      (((synCcompl (Class.cv (nb072AlphaDummy142 y H)))).fv ∪
        ((synCcompl (Class.cv (nb072AlphaDummy143 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0150 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy140 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy140 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0151 (y : Var) (H : Class) :
    (nb072AlphaDummy143 y H) ∈
      (((Class.cv (nb072AlphaDummy143 y H))).fv ∪
        ((Class.cv (nb072AlphaDummy143 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0152 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy116 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
        ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0153 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy116 A B R S_cls H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))))))).fv ∪
        ((synCcompl (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy116 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy116 A B R S_cls H) ≠ (nb072AlphaDummy124 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0152 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy116 A B R S_cls H) ≠ (nb072AlphaDummy125 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy125;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0152 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0154 (y : Var) (H : Class) :
    (nb072AlphaDummy117 y H) ∈
      (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0155 (y : Var) (H : Class) :
    (nb072AlphaDummy117 y H) ∈
      (((synCcompl (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCphi (Class.cv (nb072AlphaDummy127 y H)))))))).fv ∪ ((synCcompl
            (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy126 y H) from (by
          unfold nb072AlphaDummy126;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0154 y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy127 y H) from (by
            unfold nb072AlphaDummy127;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0154 y H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0156 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy116 A B R S_cls H) ∈
      (((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy116 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy116 A B R S_cls H) ≠ (nb072AlphaDummy124 A B R S_cls H) from
        (by
          unfold nb072AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0152 A B R S_cls H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy116 A B R S_cls H) ≠ (nb072AlphaDummy125 A B R S_cls H) from
          (by
            unfold nb072AlphaDummy125;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb072_support_mem_0152 A B R S_cls H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0157 (y : Var) (H : Class) :
    (nb072AlphaDummy117 y H) ∈
      (((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv (nb072AlphaDummy117 y H))
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy127 y H)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy126 y H) from (by
          unfold nb072AlphaDummy126;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0154 y H) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy127 y H) from (by
            unfold nb072AlphaDummy127;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0154 y H) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0158 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy125 A B R S_cls H) ∈
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0159 (y : Var) (H : Class) :
    (nb072AlphaDummy127 y H) ∈
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy127 y H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0160 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy125 A B R S_cls H) ∈
      (((synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0161 (y : Var) (H : Class) :
    (nb072AlphaDummy127 y H) ∈
      (((synCphi (Class.cv (nb072AlphaDummy127 y H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy127 y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0162 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy118 A B R S_cls H) ∈
      (((Class.cv (nb072AlphaDummy118 A B R S_cls H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0163 (y : Var) (H : Class) :
    (nb072AlphaDummy119 y H) ∈ (((Class.cv (nb072AlphaDummy119 y H))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0164 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy039 A B R S_cls H) ∈
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0165 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy041 x y H) ∈
      (((synCcompl (synCphi (Class.cv (nb072AlphaDummy041 x y H))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0166 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) :
    (nb072AlphaDummy039 A B R S_cls H) ∈
      (((synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0167 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy041 x y H) ∈
      (((synCphi (Class.cv (nb072AlphaDummy041 x y H)))).fv ∪
        ((synCphi (Class.cv (nb072AlphaDummy041 x y H)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_compact_envfresh_0000 (A : Class) (B : Class) (H : Class) :
    TEnvFresh [] ((synWf1o H A B)).fv := by exact (TEnvFresh.nil ((synWf1o H A B)).fv)

/-- Checked nominal proof certificate identified upstream as `nb072_wpp_refl_0000`. -/
@[expose]
noncomputable def nb072WppRefl0000 (A : Class) (B : Class) (H : Class) :
    TReflOn [] ((synWf1o H A B)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0000 A B H)

theorem nb072_focused_notmem_0000 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy000 A B R S_cls H) ∉ A.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb072_compact_envfresh_0001 (x : Var) (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) :
    TEnvFresh [((nb072AlphaDummy000 A B R S_cls H), x)] A.fv := by
  exact
    (TEnvFresh.consFresh (nb072AlphaDummy000 A B R S_cls H) x
      (nb072_focused_notmem_0000 A B R S_cls H) dv_A_x (TEnvFresh.nil A.fv))

/-- Checked nominal proof certificate identified upstream as `nb072_focused_refl_0000`. -/
@[expose]
noncomputable def nb072FocusedRefl0000 (x : Var) (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) :
    TReflOn [((nb072AlphaDummy000 A B R S_cls H), x)] A.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0001 x A B R S_cls H dv_A_x)

theorem nb072_focused_notmem_0001 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy001 A B R S_cls H) ∉ A.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb072_compact_envfresh_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TEnvFresh
      [((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072AlphaDummy001 A B R S_cls H) y
      (nb072_focused_notmem_0001 A B R S_cls H) dv_A_y
      (TEnvFresh.consFresh (nb072AlphaDummy000 A B R S_cls H) x
        (nb072_focused_notmem_0000 A B R S_cls H) dv_A_x (TEnvFresh.nil A.fv)))

/-- Checked nominal proof certificate identified upstream as `nb072_focused_refl_0001`. -/
@[expose]
noncomputable def nb072FocusedRefl0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn
      [((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      A.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0002 x y A B R S_cls H dv_A_x dv_A_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
