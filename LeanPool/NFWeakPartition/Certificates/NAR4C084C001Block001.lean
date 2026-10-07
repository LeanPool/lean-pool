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

/-! Certificates from `NAR4C084C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_000`. -/
@[expose]
noncomputable def nb084AlphaDummy000 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_001`. -/
@[expose]
noncomputable def nb084AlphaDummy001 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_002`. -/
@[expose]
noncomputable def nb084AlphaDummy002 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_003`. -/
@[expose]
noncomputable def nb084AlphaDummy003 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
      ((Class.cv (nb084AlphaDummy002 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_004`. -/
@[expose]
noncomputable def nb084AlphaDummy004 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
      ((Class.cv (nb084AlphaDummy002 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_005`. -/
@[expose]
noncomputable def nb084AlphaDummy005 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_006`. -/
@[expose]
noncomputable def nb084AlphaDummy006 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_007`. -/
@[expose]
noncomputable def nb084AlphaDummy007 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
      ((Class.cv (nb084AlphaDummy002 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_008`. -/
@[expose]
noncomputable def nb084AlphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_009`. -/
@[expose]
noncomputable def nb084AlphaDummy009 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
      ((Class.cv (nb084AlphaDummy004 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_010`. -/
@[expose]
noncomputable def nb084AlphaDummy010 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
      ((Class.cv (nb084AlphaDummy004 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_011`. -/
@[expose]
noncomputable def nb084AlphaDummy011 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
      ((Class.cv (nb084AlphaDummy006 x y A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_012`. -/
@[expose]
noncomputable def nb084AlphaDummy012 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
      ((Class.cv (nb084AlphaDummy006 x y A R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_013`. -/
@[expose]
noncomputable def nb084AlphaDummy013 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb084AlphaDummy009 A B R)
            (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCphi (Class.cv (nb084AlphaDummy010 A B R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy004 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_014`. -/
@[expose]
noncomputable def nb084AlphaDummy014 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb084AlphaDummy011 x y A R)
            (synWrex (nb084AlphaDummy012 x y A R) (Class.cv (nb084AlphaDummy005 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy006 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_015`. -/
@[expose]
noncomputable def nb084AlphaDummy015 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb084AlphaDummy009 A B R)
          (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy003 A B R))
            (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
              (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))).fv ∪
      ((Class.cab (nb084AlphaDummy009 A B R)
          (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy003 A B R))
            (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
              (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_016`. -/
@[expose]
noncomputable def nb084AlphaDummy016 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb084AlphaDummy011 x y A R)
          (synWrex (nb084AlphaDummy012 x y A R) (Class.cv (nb084AlphaDummy005 x y A R))
            (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
              (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))).fv ∪
      ((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
            (Class.cv (nb084AlphaDummy005 x y A R))
            (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
              (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_017`. -/
@[expose]
noncomputable def nb084AlphaDummy017 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy010 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_018`. -/
@[expose]
noncomputable def nb084AlphaDummy018 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy010 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_019`. -/
@[expose]
noncomputable def nb084AlphaDummy019 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy012 x y A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_020`. -/
@[expose]
noncomputable def nb084AlphaDummy020 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy012 x y A R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_021`. -/
@[expose]
noncomputable def nb084AlphaDummy021 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb084AlphaDummy017 A B R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb084AlphaDummy017 A B R)) (synC1c))).fv ∪
      ((Class.cv (nb084AlphaDummy017 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_022`. -/
@[expose]
noncomputable def nb084AlphaDummy022 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb084AlphaDummy019 x y A R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb084AlphaDummy019 x y A R)) (synC1c))).fv ∪
      ((Class.cv (nb084AlphaDummy019 x y A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_023`. -/
@[expose]
noncomputable def nb084AlphaDummy023 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_024`. -/
@[expose]
noncomputable def nb084AlphaDummy024 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_025`. -/
@[expose]
noncomputable def nb084AlphaDummy025 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_026`. -/
@[expose]
noncomputable def nb084AlphaDummy026 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_027`. -/
@[expose]
noncomputable def nb084AlphaDummy027 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_028`. -/
@[expose]
noncomputable def nb084AlphaDummy028 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_029`. -/
@[expose]
noncomputable def nb084AlphaDummy029 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb084AlphaDummy024 A B R))
          (Class.cv (nb084AlphaDummy025 A B R)))).fv ∪
      ((synCnin (Class.cv (nb084AlphaDummy024 A B R))
          (Class.cv (nb084AlphaDummy025 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_030`. -/
@[expose]
noncomputable def nb084AlphaDummy030 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
          (Class.cv (nb084AlphaDummy028 x y A R)))).fv ∪
      ((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
          (Class.cv (nb084AlphaDummy028 x y A R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_031`. -/
@[expose]
noncomputable def nb084AlphaDummy031 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
      ((Class.cv (nb084AlphaDummy025 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_032`. -/
@[expose]
noncomputable def nb084AlphaDummy032 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
      ((Class.cv (nb084AlphaDummy028 x y A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_033`. -/
@[expose]
noncomputable def nb084AlphaDummy033 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb084AlphaDummy024 A B R)))).fv ∪
      ((synCcompl (Class.cv (nb084AlphaDummy025 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_034`. -/
@[expose]
noncomputable def nb084AlphaDummy034 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb084AlphaDummy027 x y A R)))).fv ∪
      ((synCcompl (Class.cv (nb084AlphaDummy028 x y A R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_035`. -/
@[expose]
noncomputable def nb084AlphaDummy035 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
      ((Class.cv (nb084AlphaDummy024 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_036`. -/
@[expose]
noncomputable def nb084AlphaDummy036 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
      ((Class.cv (nb084AlphaDummy027 x y A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_037`. -/
@[expose]
noncomputable def nb084AlphaDummy037 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb084AlphaDummy025 A B R))).fv ∪
      ((Class.cv (nb084AlphaDummy025 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_038`. -/
@[expose]
noncomputable def nb084AlphaDummy038 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb084AlphaDummy028 x y A R))).fv ∪
      ((Class.cv (nb084AlphaDummy028 x y A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_039`. -/
@[expose]
noncomputable def nb084AlphaDummy039 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb084AlphaDummy009 A B R)
          (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy004 A B R))
            (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
              (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb084AlphaDummy009 A B R)
          (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy004 A B R))
            (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
              (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_040`. -/
@[expose]
noncomputable def nb084AlphaDummy040 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb084AlphaDummy011 x y A R)
          (synWrex (nb084AlphaDummy012 x y A R) (Class.cv (nb084AlphaDummy006 x y A R))
            (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
              (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb084AlphaDummy011 x y A R)
          (synWrex (nb084AlphaDummy012 x y A R) (Class.cv (nb084AlphaDummy006 x y A R))
            (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
              (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_041`. -/
@[expose]
noncomputable def nb084AlphaDummy041 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb084AlphaDummy010 A B R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_042`. -/
@[expose]
noncomputable def nb084AlphaDummy042 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_043`. -/
@[expose]
noncomputable def nb084AlphaDummy043 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb084AlphaDummy010 A B R)))).fv ∪
      ((synCphi (Class.cv (nb084AlphaDummy010 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb084_alpha_dummy_044`. -/
@[expose]
noncomputable def nb084AlphaDummy044 (x : Var) (y : Var) (A : Class) (R : Class) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb084AlphaDummy012 x y A R)))).fv ∪
      ((synCphi (Class.cv (nb084AlphaDummy012 x y A R)))).fv) 0)

theorem nb084_fresh_000 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy015 A B R) ∉
      (((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))).fv ∪
        ((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))).fv) :=
  by
  simpa only [nb084AlphaDummy015] using
    freshVar_not_mem
      (((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))).fv ∪
        ((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))).fv)
      0

theorem nb084_fresh_001 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy039 A B R) ∉
      (((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy004 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb084AlphaDummy009 A B R)
            (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy004 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb084AlphaDummy039] using
    freshVar_not_mem
      (((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy004 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb084AlphaDummy009 A B R)
            (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy004 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb084_fresh_002 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy016 x y A R) ∉
      (((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy005 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))).fv ∪
        ((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy005 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))).fv) :=
  by
  simpa only [nb084AlphaDummy016] using
    freshVar_not_mem
      (((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy005 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))).fv ∪
        ((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy005 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))).fv)
      0

theorem nb084_fresh_003 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy040 x y A R) ∉
      (((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy006 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb084AlphaDummy011 x y A R)
            (synWrex (nb084AlphaDummy012 x y A R) (Class.cv (nb084AlphaDummy006 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb084AlphaDummy040] using
    freshVar_not_mem
      (((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy006 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb084AlphaDummy011 x y A R)
            (synWrex (nb084AlphaDummy012 x y A R) (Class.cv (nb084AlphaDummy006 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb084_fresh_004 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy007 A B R) ∉
      (((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv)
      0

theorem nb084_fresh_005 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy009 A B R) ∉
      (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy004 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy009] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy004 A B R))).fv)
      0

theorem nb084_fresh_006 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy010 A B R) ∉
      (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy004 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy010] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy004 A B R))).fv)
      1

theorem nb084_distinct_007 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy009 A B R) ≠ (nb084AlphaDummy010 A B R) := by
  simpa only [nb084AlphaDummy009, nb084AlphaDummy010] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy004 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb084_fresh_008 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy011 x y A R) ∉
      (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy006 x y A R))).fv) :=
  by
  simpa only [nb084AlphaDummy011] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy006 x y A R))).fv)
      0

theorem nb084_fresh_009 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy012 x y A R) ∉
      (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy006 x y A R))).fv) :=
  by
  simpa only [nb084AlphaDummy012] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy006 x y A R))).fv)
      1

theorem nb084_distinct_010 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy011 x y A R) ≠ (nb084AlphaDummy012 x y A R) := by
  simpa only [nb084AlphaDummy011, nb084AlphaDummy012] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy006 x y A R))).fv) (i := 0) (j := 1) (by decide))

theorem nb084_fresh_011 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy017 A B R) ∉ (((Class.cv (nb084AlphaDummy010 A B R))).fv) := by
  simpa only [nb084AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy010 A B R))).fv) 0

theorem nb084_fresh_012 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy018 A B R) ∉ (((Class.cv (nb084AlphaDummy010 A B R))).fv) := by
  simpa only [nb084AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy010 A B R))).fv) 1

theorem nb084_distinct_013 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy017 A B R) ≠ (nb084AlphaDummy018 A B R) := by
  simpa only [nb084AlphaDummy017, nb084AlphaDummy018] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy010 A B R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb084_fresh_014 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy019 x y A R) ∉ (((Class.cv (nb084AlphaDummy012 x y A R))).fv) :=
  by
  simpa only [nb084AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy012 x y A R))).fv) 0

theorem nb084_fresh_015 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy020 x y A R) ∉ (((Class.cv (nb084AlphaDummy012 x y A R))).fv) :=
  by
  simpa only [nb084AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy012 x y A R))).fv) 1

theorem nb084_distinct_016 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy020 x y A R) := by
  simpa only [nb084AlphaDummy019, nb084AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy012 x y A R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb084_fresh_017 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy023 A B R) ∉
      (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb084AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) 0

theorem nb084_fresh_018 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy024 A B R) ∉
      (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb084AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) 1

theorem nb084_fresh_019 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy025 A B R) ∉
      (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb084AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) 2

theorem nb084_distinct_020 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy023 A B R) ≠ (nb084AlphaDummy024 A B R) := by
  simpa only [nb084AlphaDummy023, nb084AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb084_distinct_021 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy023 A B R) ≠ (nb084AlphaDummy025 A B R) := by
  simpa only [nb084AlphaDummy023, nb084AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb084_distinct_022 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy024 A B R) ≠ (nb084AlphaDummy025 A B R) := by
  simpa only [nb084AlphaDummy024, nb084AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb084_fresh_023 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy026 x y A R) ∉
      (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb084AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) 0

theorem nb084_fresh_024 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy027 x y A R) ∉
      (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb084AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) 1

theorem nb084_fresh_025 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy028 x y A R) ∉
      (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb084AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) 2

theorem nb084_distinct_026 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy026 x y A R) ≠ (nb084AlphaDummy027 x y A R) := by
  simpa only [nb084AlphaDummy026, nb084AlphaDummy027] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb084_distinct_027 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy026 x y A R) ≠ (nb084AlphaDummy028 x y A R) := by
  simpa only [nb084AlphaDummy026, nb084AlphaDummy028] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb084_distinct_028 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy028 x y A R) := by
  simpa only [nb084AlphaDummy027, nb084AlphaDummy028] using
    (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb084_fresh_029 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy035 A B R) ∉
      (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy024 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy024 A B R))).fv)
      0

theorem nb084_fresh_030 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy031 A B R) ∉
      (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy025 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy025 A B R))).fv)
      0

theorem nb084_fresh_031 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy037 A B R) ∉
      (((Class.cv (nb084AlphaDummy025 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy025 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy025 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy025 A B R))).fv)
      0

theorem nb084_fresh_032 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy036 x y A R) ∉
      (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy027 x y A R))).fv) :=
  by
  simpa only [nb084AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy027 x y A R))).fv)
      0

theorem nb084_fresh_033 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy032 x y A R) ∉
      (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy028 x y A R))).fv) :=
  by
  simpa only [nb084AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy028 x y A R))).fv)
      0

theorem nb084_fresh_034 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy038 x y A R) ∉
      (((Class.cv (nb084AlphaDummy028 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy028 x y A R))).fv) :=
  by
  simpa only [nb084AlphaDummy038] using
    freshVar_not_mem
      (((Class.cv (nb084AlphaDummy028 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy028 x y A R))).fv)
      0

theorem nb084_fresh_035 (x : Var) (y : Var) :
    (nb084AlphaDummy008 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb084AlphaDummy008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb084_fresh_036 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy021 A B R) ∉
      (((Wff.classMem (Class.cv (nb084AlphaDummy017 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb084AlphaDummy017 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb084AlphaDummy017 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb084AlphaDummy017 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb084AlphaDummy017 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb084AlphaDummy017 A B R))).fv)
      0

theorem nb084_fresh_037 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy022 x y A R) ∉
      (((Wff.classMem (Class.cv (nb084AlphaDummy019 x y A R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb084AlphaDummy019 x y A R)) (synC1c))).fv ∪
        ((Class.cv (nb084AlphaDummy019 x y A R))).fv) :=
  by
  simpa only [nb084AlphaDummy022] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb084AlphaDummy019 x y A R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb084AlphaDummy019 x y A R)) (synC1c))).fv ∪
        ((Class.cv (nb084AlphaDummy019 x y A R))).fv)
      0

theorem nb084_fresh_038 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy013 A B R) ∉
      (((synCcompl (Class.cab (nb084AlphaDummy009 A B R)
              (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCphi (Class.cv (nb084AlphaDummy010 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
                (Class.cv (nb084AlphaDummy004 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb084AlphaDummy013] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb084AlphaDummy009 A B R)
              (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCphi (Class.cv (nb084AlphaDummy010 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
                (Class.cv (nb084AlphaDummy004 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb084_fresh_039 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy014 x y A R) ∉
      (((synCcompl (Class.cab (nb084AlphaDummy011 x y A R)
              (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy005 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy006 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb084AlphaDummy014] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb084AlphaDummy011 x y A R)
              (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy005 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy006 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb084_fresh_040 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy033 A B R) ∉
      (((synCcompl (Class.cv (nb084AlphaDummy024 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb084AlphaDummy025 A B R)))).fv) :=
  by
  simpa only [nb084AlphaDummy033] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb084AlphaDummy024 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb084AlphaDummy025 A B R)))).fv)
      0

theorem nb084_fresh_041 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy034 x y A R) ∉
      (((synCcompl (Class.cv (nb084AlphaDummy027 x y A R)))).fv ∪
        ((synCcompl (Class.cv (nb084AlphaDummy028 x y A R)))).fv) :=
  by
  simpa only [nb084AlphaDummy034] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb084AlphaDummy027 x y A R)))).fv ∪
        ((synCcompl (Class.cv (nb084AlphaDummy028 x y A R)))).fv)
      0

theorem nb084_fresh_042 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy041 A B R) ∉
      (((synCcompl (synCphi (Class.cv (nb084AlphaDummy010 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb084AlphaDummy041] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb084AlphaDummy010 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb084_fresh_043 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy042 x y A R) ∉
      (((synCcompl (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb084AlphaDummy042] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb084_fresh_044 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy029 A B R) ∉
      (((synCnin (Class.cv (nb084AlphaDummy024 A B R))
            (Class.cv (nb084AlphaDummy025 A B R)))).fv ∪
        ((synCnin (Class.cv (nb084AlphaDummy024 A B R))
            (Class.cv (nb084AlphaDummy025 A B R)))).fv) :=
  by
  simpa only [nb084AlphaDummy029] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb084AlphaDummy024 A B R))
            (Class.cv (nb084AlphaDummy025 A B R)))).fv ∪
        ((synCnin (Class.cv (nb084AlphaDummy024 A B R))
            (Class.cv (nb084AlphaDummy025 A B R)))).fv)
      0

theorem nb084_fresh_045 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy030 x y A R) ∉
      (((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
            (Class.cv (nb084AlphaDummy028 x y A R)))).fv ∪
        ((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
            (Class.cv (nb084AlphaDummy028 x y A R)))).fv) :=
  by
  simpa only [nb084AlphaDummy030] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
            (Class.cv (nb084AlphaDummy028 x y A R)))).fv ∪
        ((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
            (Class.cv (nb084AlphaDummy028 x y A R)))).fv)
      0

theorem nb084_fresh_046 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy043 A B R) ∉
      (((synCphi (Class.cv (nb084AlphaDummy010 A B R)))).fv ∪
        ((synCphi (Class.cv (nb084AlphaDummy010 A B R)))).fv) :=
  by
  simpa only [nb084AlphaDummy043] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb084AlphaDummy010 A B R)))).fv ∪
        ((synCphi (Class.cv (nb084AlphaDummy010 A B R)))).fv)
      0

theorem nb084_fresh_047 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy044 x y A R) ∉
      (((synCphi (Class.cv (nb084AlphaDummy012 x y A R)))).fv ∪
        ((synCphi (Class.cv (nb084AlphaDummy012 x y A R)))).fv) :=
  by
  simpa only [nb084AlphaDummy044] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb084AlphaDummy012 x y A R)))).fv ∪
        ((synCphi (Class.cv (nb084AlphaDummy012 x y A R)))).fv)
      0

theorem nb084_fresh_048 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy003 A B R) ∉
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy003] using
    freshVar_not_mem
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv)
      0

theorem nb084_fresh_049 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy004 A B R) ∉
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv) :=
  by
  simpa only [nb084AlphaDummy004] using
    freshVar_not_mem
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv)
      1

theorem nb084_distinct_050 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy004 A B R) := by
  simpa only [nb084AlphaDummy003, nb084AlphaDummy004] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb084_fresh_051 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy005 x y A R) ∉
      ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  simpa only [nb084AlphaDummy005] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb084_fresh_052 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy006 x y A R) ∉
      ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  simpa only [nb084AlphaDummy006] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb084_distinct_053 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy006 x y A R) := by
  simpa only [nb084AlphaDummy005, nb084AlphaDummy006] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb084_fresh_054 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy000 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb084AlphaDummy000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb084_fresh_055 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy001 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb084AlphaDummy001] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 1

theorem nb084_fresh_056 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy002 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb084AlphaDummy002] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 2

theorem nb084_distinct_057 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy000 A B R) ≠ (nb084AlphaDummy001 A B R) := by
  simpa only [nb084AlphaDummy000, nb084AlphaDummy001] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv) (i := 0) (j := 1) (by decide))

theorem nb084_distinct_058 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy000 A B R) ≠ (nb084AlphaDummy002 A B R) := by
  simpa only [nb084AlphaDummy000, nb084AlphaDummy002] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv) (i := 0) (j := 2) (by decide))

theorem nb084_distinct_059 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy001 A B R) ≠ (nb084AlphaDummy002 A B R) := by
  simpa only [nb084AlphaDummy001, nb084AlphaDummy002] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv) (i := 1) (j := 2) (by decide))

theorem nb084_support_mem_0000 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy001 A B R) ∈
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0001 (x : Var) (y : Var) (A : Class) (R : Class) :
    x ∈ ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0002 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy001 A B R) ∈
      (((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0003 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0004 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy002 A B R) ∈
      ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0005 (x : Var) (y : Var) (A : Class) (R : Class) :
    y ∈ ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0006 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy002 A B R) ∈
      (((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy002 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0007 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0008 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy003 A B R) ∈
      (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy004 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0009 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy003 A B R) ∈
      (((synCcompl (Class.cab (nb084AlphaDummy009 A B R)
              (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCphi (Class.cv (nb084AlphaDummy010 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
                (Class.cv (nb084AlphaDummy004 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy009 A B R) from (by
          unfold nb084AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0008 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy010 A B R) from (by
            unfold nb084AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0008 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0010 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy005 x y A R) ∈
      (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy006 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0011 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy005 x y A R) ∈
      (((synCcompl (Class.cab (nb084AlphaDummy011 x y A R)
              (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy005 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy006 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy011 x y A R) from (by
          unfold nb084AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy012 x y A R) from (by
            unfold nb084AlphaDummy012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0012 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy003 A B R) ∈
      (((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))).fv ∪
        ((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy009 A B R) from (by
          unfold nb084AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0008 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy010 A B R) from (by
            unfold nb084AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0008 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0013 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy005 x y A R) ∈
      (((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy005 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))).fv ∪
        ((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy005 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy011 x y A R) from (by
          unfold nb084AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy012 x y A R) from (by
            unfold nb084AlphaDummy012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0014 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy010 A B R) ∈ (((Class.cv (nb084AlphaDummy010 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0015 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy012 x y A R) ∈ (((Class.cv (nb084AlphaDummy012 x y A R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0016 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy017 A B R) ∈
      (((Wff.classMem (Class.cv (nb084AlphaDummy017 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb084AlphaDummy017 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb084AlphaDummy017 A B R))).fv) :=
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

theorem nb084_support_mem_0017 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy019 x y A R) ∈
      (((Wff.classMem (Class.cv (nb084AlphaDummy019 x y A R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb084AlphaDummy019 x y A R)) (synC1c))).fv ∪
        ((Class.cv (nb084AlphaDummy019 x y A R))).fv) :=
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

theorem nb084_support_mem_0018 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy017 A B R) ∈
      (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0019 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy019 x y A R) ∈
      (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0020 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy024 A B R) ∈
      (((synCnin (Class.cv (nb084AlphaDummy024 A B R))
            (Class.cv (nb084AlphaDummy025 A B R)))).fv ∪
        ((synCnin (Class.cv (nb084AlphaDummy024 A B R))
            (Class.cv (nb084AlphaDummy025 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0021 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy027 x y A R) ∈
      (((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
            (Class.cv (nb084AlphaDummy028 x y A R)))).fv ∪
        ((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
            (Class.cv (nb084AlphaDummy028 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0022 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy024 A B R) ∈
      (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy025 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0023 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy027 x y A R) ∈
      (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy028 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0024 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy025 A B R) ∈
      (((synCnin (Class.cv (nb084AlphaDummy024 A B R))
            (Class.cv (nb084AlphaDummy025 A B R)))).fv ∪
        ((synCnin (Class.cv (nb084AlphaDummy024 A B R))
            (Class.cv (nb084AlphaDummy025 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0025 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy028 x y A R) ∈
      (((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
            (Class.cv (nb084AlphaDummy028 x y A R)))).fv ∪
        ((synCnin (Class.cv (nb084AlphaDummy027 x y A R))
            (Class.cv (nb084AlphaDummy028 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0026 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy025 A B R) ∈
      (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy025 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0027 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy028 x y A R) ∈
      (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy028 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0028 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy024 A B R) ∈
      (((synCcompl (Class.cv (nb084AlphaDummy024 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb084AlphaDummy025 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0029 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy027 x y A R) ∈
      (((synCcompl (Class.cv (nb084AlphaDummy027 x y A R)))).fv ∪
        ((synCcompl (Class.cv (nb084AlphaDummy028 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0030 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy024 A B R) ∈
      (((Class.cv (nb084AlphaDummy024 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy024 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0031 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy027 x y A R) ∈
      (((Class.cv (nb084AlphaDummy027 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy027 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0032 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy025 A B R) ∈
      (((synCcompl (Class.cv (nb084AlphaDummy024 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb084AlphaDummy025 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0033 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy028 x y A R) ∈
      (((synCcompl (Class.cv (nb084AlphaDummy027 x y A R)))).fv ∪
        ((synCcompl (Class.cv (nb084AlphaDummy028 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0034 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy025 A B R) ∈
      (((Class.cv (nb084AlphaDummy025 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy025 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0035 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy028 x y A R) ∈
      (((Class.cv (nb084AlphaDummy028 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy028 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0036 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy004 A B R) ∈
      (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
        ((Class.cv (nb084AlphaDummy004 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0037 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy004 A B R) ∈
      (((synCcompl (Class.cab (nb084AlphaDummy009 A B R)
              (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCphi (Class.cv (nb084AlphaDummy010 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
                (Class.cv (nb084AlphaDummy004 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084AlphaDummy004 A B R) ≠ (nb084AlphaDummy009 A B R) from (by
          unfold nb084AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084AlphaDummy004 A B R) ≠ (nb084AlphaDummy010 A B R) from (by
            unfold nb084AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0038 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy006 x y A R) ∈
      (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
        ((Class.cv (nb084AlphaDummy006 x y A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0039 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy006 x y A R) ∈
      (((synCcompl (Class.cab (nb084AlphaDummy011 x y A R)
              (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy005 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy006 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084AlphaDummy006 x y A R) ≠ (nb084AlphaDummy011 x y A R) from (by
          unfold nb084AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084AlphaDummy006 x y A R) ≠ (nb084AlphaDummy012 x y A R) from (by
            unfold nb084AlphaDummy012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0040 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy004 A B R) ∈
      (((Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy004 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb084AlphaDummy009 A B R)
            (synWrex (nb084AlphaDummy010 A B R) (Class.cv (nb084AlphaDummy004 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084AlphaDummy004 A B R) ≠ (nb084AlphaDummy009 A B R) from (by
          unfold nb084AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084AlphaDummy004 A B R) ≠ (nb084AlphaDummy010 A B R) from (by
            unfold nb084AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0041 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy006 x y A R) ∈
      (((Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy006 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb084AlphaDummy011 x y A R)
            (synWrex (nb084AlphaDummy012 x y A R) (Class.cv (nb084AlphaDummy006 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb084AlphaDummy006 x y A R) ≠ (nb084AlphaDummy011 x y A R) from (by
          unfold nb084AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb084AlphaDummy006 x y A R) ≠ (nb084AlphaDummy012 x y A R) from (by
            unfold nb084AlphaDummy012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb084_support_mem_0042 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy010 A B R) ∈
      (((synCcompl (synCphi (Class.cv (nb084AlphaDummy010 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0043 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy012 x y A R) ∈
      (((synCcompl (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_support_mem_0044 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy010 A B R) ∈
      (((synCphi (Class.cv (nb084AlphaDummy010 A B R)))).fv ∪
        ((synCphi (Class.cv (nb084AlphaDummy010 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C084C001Part002`. -/


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

theorem nb084_support_mem_0045 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy012 x y A R) ∈
      (((synCphi (Class.cv (nb084AlphaDummy012 x y A R)))).fv ∪
        ((synCphi (Class.cv (nb084AlphaDummy012 x y A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_focused_notmem_0000 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy000 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_compact_envfresh_0000 (A : Class) (B : Class) (R : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) : TEnvFresh [((nb084AlphaDummy000 A B R), d)] A.fv := by
  exact
    (TEnvFresh.consFresh (nb084AlphaDummy000 A B R) d (nb084_focused_notmem_0000 A B R)
      dv_A_d (TEnvFresh.nil A.fv))

/-- Checked nominal proof certificate identified upstream as `nb084_focused_refl_0000`. -/
@[expose]
noncomputable def nb084FocusedRefl0000 (A : Class) (B : Class) (R : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) : TReflOn [((nb084AlphaDummy000 A B R), d)] A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0000 A B R d dv_A_d)

theorem nb084_focused_notmem_0001 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy001 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_focused_notmem_0002 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy000 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_compact_envfresh_0001 (x : Var) (A : Class) (B : Class) (R : Class)
    (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) :
    TEnvFresh [((nb084AlphaDummy001 A B R), x), ((nb084AlphaDummy000 A B R), d)]
      B.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084AlphaDummy001 A B R) x (nb084_focused_notmem_0001 A B R)
      dv_B_x (TEnvFresh.consFresh (nb084AlphaDummy000 A B R) d
        (nb084_focused_notmem_0002 A B R) dv_B_d (TEnvFresh.nil B.fv)))

/-- Checked nominal proof certificate identified upstream as `nb084_focused_refl_0001`. -/
@[expose]
noncomputable def nb084FocusedRefl0001 (x : Var) (A : Class) (B : Class) (R : Class)
    (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) :
    TReflOn [((nb084AlphaDummy001 A B R), x), ((nb084AlphaDummy000 A B R), d)]
      B.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0001 x A B R d dv_B_d dv_B_x)

theorem nb084_focused_notmem_0003 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy002 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_compact_envfresh_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) :
    TEnvFresh
      [((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      B.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084AlphaDummy002 A B R) y (nb084_focused_notmem_0003 A B R)
      dv_B_y (TEnvFresh.consFresh (nb084AlphaDummy001 A B R) x
        (nb084_focused_notmem_0001 A B R) dv_B_x
        (TEnvFresh.consFresh (nb084AlphaDummy000 A B R) d
          (nb084_focused_notmem_0002 A B R) dv_B_d (TEnvFresh.nil B.fv))))

/-- Checked nominal proof certificate identified upstream as `nb084_focused_refl_0002`. -/
@[expose]
noncomputable def nb084FocusedRefl0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) :
    TReflOn
      [((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      B.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0002 x y A B R d dv_B_d dv_B_x dv_B_y)

theorem nb084_focused_notmem_0004 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy003 A B R) ∉ A.fv :=
  by
  change
    freshVar
        ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
          ((Class.cv (nb084AlphaDummy002 A B R))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0005 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy005 x y A R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0006 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy002 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_focused_notmem_0007 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy001 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_compact_envfresh_0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TEnvFresh
      [((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084AlphaDummy003 A B R) (nb084AlphaDummy005 x y A R)
      (nb084_focused_notmem_0004 A B R) (nb084_focused_notmem_0005 x y A R)
      (TEnvFresh.consFresh (nb084AlphaDummy002 A B R) y
        (nb084_focused_notmem_0006 A B R) dv_A_y
        (TEnvFresh.consFresh (nb084AlphaDummy001 A B R) x
          (nb084_focused_notmem_0007 A B R) dv_A_x
          (TEnvFresh.consFresh (nb084AlphaDummy000 A B R) d
            (nb084_focused_notmem_0000 A B R) dv_A_d (TEnvFresh.nil A.fv)))))

/-- Checked nominal proof certificate identified upstream as `nb084_focused_refl_0003`. -/
@[expose]
noncomputable def nb084FocusedRefl0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn
      [((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0003 x y A B R d dv_A_d dv_A_x dv_A_y)

theorem nb084_focused_notmem_0008 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy004 A B R) ∉ A.fv :=
  by
  change
    freshVar
        ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
          ((Class.cv (nb084AlphaDummy002 A B R))).fv)
        1 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0009 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy006 x y A R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_compact_envfresh_0004 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TEnvFresh
      [((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084AlphaDummy004 A B R) (nb084AlphaDummy006 x y A R)
      (nb084_focused_notmem_0008 A B R) (nb084_focused_notmem_0009 x y A R)
      (TEnvFresh.consFresh (nb084AlphaDummy003 A B R) (nb084AlphaDummy005 x y A R)
        (nb084_focused_notmem_0004 A B R) (nb084_focused_notmem_0005 x y A R)
        (TEnvFresh.consFresh (nb084AlphaDummy002 A B R) y
          (nb084_focused_notmem_0006 A B R) dv_A_y
          (TEnvFresh.consFresh (nb084AlphaDummy001 A B R) x
            (nb084_focused_notmem_0007 A B R) dv_A_x
            (TEnvFresh.consFresh (nb084AlphaDummy000 A B R) d
              (nb084_focused_notmem_0000 A B R) dv_A_d (TEnvFresh.nil A.fv))))))

/-- Checked nominal proof certificate identified upstream as `nb084_focused_refl_0004`. -/
@[expose]
noncomputable def nb084FocusedRefl0004 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn
      [((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0004 x y A B R d dv_A_d dv_A_x dv_A_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
