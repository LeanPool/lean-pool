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

/-! Certificates from `NAR5H088P001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_000`. -/
@[expose]
noncomputable def nb088AlphaDummy000 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_001`. -/
@[expose]
noncomputable def nb088AlphaDummy001 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪ ((synCpw1 (synCpw1 C))).fv ∪
      ((synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_002`. -/
@[expose]
noncomputable def nb088AlphaDummy002 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 C))).fv ∪
      ((synCfdrowfib R A B (Class.cv u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_003`. -/
@[expose]
noncomputable def nb088AlphaDummy003 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪
        ({(nb088AlphaDummy001 A B C R)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb088AlphaDummy000 A B C R)) (synCpw1 (synCpw1 C)))
          (Wff.classEq (Class.cv (nb088AlphaDummy001 A B C R))
            (synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_004`. -/
@[expose]
noncomputable def nb088AlphaDummy004 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (({ u } : Finset Var) ∪ ({(nb088AlphaDummy002 u A B C R)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 C)))
          (Wff.classEq (Class.cv (nb088AlphaDummy002 u A B C R))
            (synCfdrowfib R A B (Class.cv u))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_005`. -/
@[expose]
noncomputable def nb088AlphaDummy005 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy001 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_006`. -/
@[expose]
noncomputable def nb088AlphaDummy006 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy001 A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_007`. -/
@[expose]
noncomputable def nb088AlphaDummy007 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_008`. -/
@[expose]
noncomputable def nb088AlphaDummy008 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_009`. -/
@[expose]
noncomputable def nb088AlphaDummy009 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb088AlphaDummy005 A B C R)
            (synWrex (nb088AlphaDummy006 A B C R) (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_010`. -/
@[expose]
noncomputable def nb088AlphaDummy010 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_011`. -/
@[expose]
noncomputable def nb088AlphaDummy011 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb088AlphaDummy005 A B C R)
          (synWrex (nb088AlphaDummy006 A B C R) (Class.cv (nb088AlphaDummy000 A B C R))
            (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
              (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))))).fv ∪
      ((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
            (Class.cv (nb088AlphaDummy000 A B C R))
            (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
              (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_012`. -/
@[expose]
noncomputable def nb088AlphaDummy012 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cab (nb088AlphaDummy007 u A B C R)
          (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
            (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
              (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))))).fv ∪
      ((Class.cab (nb088AlphaDummy007 u A B C R)
          (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
            (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
              (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_013`. -/
@[expose]
noncomputable def nb088AlphaDummy013 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy006 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_014`. -/
@[expose]
noncomputable def nb088AlphaDummy014 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy006 A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_015`. -/
@[expose]
noncomputable def nb088AlphaDummy015 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv (nb088AlphaDummy008 u A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_016`. -/
@[expose]
noncomputable def nb088AlphaDummy016 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv (nb088AlphaDummy008 u A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_017`. -/
@[expose]
noncomputable def nb088AlphaDummy017 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb088AlphaDummy013 A B C R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb088AlphaDummy013 A B C R)) (synC1c))).fv ∪
      ((Class.cv (nb088AlphaDummy013 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_018`. -/
@[expose]
noncomputable def nb088AlphaDummy018 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb088AlphaDummy015 u A B C R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb088AlphaDummy015 u A B C R)) (synC1c))).fv ∪
      ((Class.cv (nb088AlphaDummy015 u A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_019`. -/
@[expose]
noncomputable def nb088AlphaDummy019 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_020`. -/
@[expose]
noncomputable def nb088AlphaDummy020 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_021`. -/
@[expose]
noncomputable def nb088AlphaDummy021 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_022`. -/
@[expose]
noncomputable def nb088AlphaDummy022 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_023`. -/
@[expose]
noncomputable def nb088AlphaDummy023 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_024`. -/
@[expose]
noncomputable def nb088AlphaDummy024 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_025`. -/
@[expose]
noncomputable def nb088AlphaDummy025 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
          (Class.cv (nb088AlphaDummy021 A B C R)))).fv ∪
      ((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
          (Class.cv (nb088AlphaDummy021 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_026`. -/
@[expose]
noncomputable def nb088AlphaDummy026 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
          (Class.cv (nb088AlphaDummy024 u A B C R)))).fv ∪
      ((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
          (Class.cv (nb088AlphaDummy024 u A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_027`. -/
@[expose]
noncomputable def nb088AlphaDummy027 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy021 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_028`. -/
@[expose]
noncomputable def nb088AlphaDummy028 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy024 u A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_029`. -/
@[expose]
noncomputable def nb088AlphaDummy029 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb088AlphaDummy020 A B C R)))).fv ∪
      ((synCcompl (Class.cv (nb088AlphaDummy021 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_030`. -/
@[expose]
noncomputable def nb088AlphaDummy030 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb088AlphaDummy023 u A B C R)))).fv ∪
      ((synCcompl (Class.cv (nb088AlphaDummy024 u A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_031`. -/
@[expose]
noncomputable def nb088AlphaDummy031 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy020 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_032`. -/
@[expose]
noncomputable def nb088AlphaDummy032 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy023 u A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_033`. -/
@[expose]
noncomputable def nb088AlphaDummy033 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy021 A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy021 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_034`. -/
@[expose]
noncomputable def nb088AlphaDummy034 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cv (nb088AlphaDummy024 u A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy024 u A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_035`. -/
@[expose]
noncomputable def nb088AlphaDummy035 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb088AlphaDummy005 A B C R)
          (synWrex (nb088AlphaDummy006 A B C R) (Class.cv (nb088AlphaDummy001 A B C R))
            (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
              (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy005 A B C R)
          (synWrex (nb088AlphaDummy006 A B C R) (Class.cv (nb088AlphaDummy001 A B C R))
            (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
              (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_036`. -/
@[expose]
noncomputable def nb088AlphaDummy036 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((Class.cab (nb088AlphaDummy007 u A B C R)
          (synWrex (nb088AlphaDummy008 u A B C R)
            (Class.cv (nb088AlphaDummy002 u A B C R))
            (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
              (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy007 u A B C R)
          (synWrex (nb088AlphaDummy008 u A B C R)
            (Class.cv (nb088AlphaDummy002 u A B C R))
            (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
              (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_037`. -/
@[expose]
noncomputable def nb088AlphaDummy037 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_038`. -/
@[expose]
noncomputable def nb088AlphaDummy038 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_039`. -/
@[expose]
noncomputable def nb088AlphaDummy039 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb088AlphaDummy006 A B C R)))).fv ∪
      ((synCphi (Class.cv (nb088AlphaDummy006 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_040`. -/
@[expose]
noncomputable def nb088AlphaDummy040 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))).fv ∪
      ((synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_041`. -/
@[expose]
noncomputable def nb088AlphaDummy041 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088AlphaDummy000 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_042`. -/
@[expose]
noncomputable def nb088AlphaDummy042 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_043`. -/
@[expose]
noncomputable def nb088AlphaDummy043 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
      ((Class.cv (nb088AlphaDummy000 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_044`. -/
@[expose]
noncomputable def nb088AlphaDummy044 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
      ((Class.cv (nb088AlphaDummy000 A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_045`. -/
@[expose]
noncomputable def nb088AlphaDummy045 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_046`. -/
@[expose]
noncomputable def nb088AlphaDummy046 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_047`. -/
@[expose]
noncomputable def nb088AlphaDummy047 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb088AlphaDummy043 A B C R)
            (synWrex (nb088AlphaDummy044 A B C R)
              (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_048`. -/
@[expose]
noncomputable def nb088AlphaDummy048 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb088AlphaDummy045 u A B R)
            (synWrex (nb088AlphaDummy046 u A B R)
              (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb088AlphaDummy045 u A B R)
            (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_049`. -/
@[expose]
noncomputable def nb088AlphaDummy049 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb088AlphaDummy043 A B C R)
          (synWrex (nb088AlphaDummy044 A B C R)
            (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
            (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
              (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))))).fv ∪
      ((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
            (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
            (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
              (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_050`. -/
@[expose]
noncomputable def nb088AlphaDummy050 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb088AlphaDummy045 u A B R)
          (synWrex (nb088AlphaDummy046 u A B R)
            (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
            (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
              (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))))).fv ∪
      ((Class.cab (nb088AlphaDummy045 u A B R) (synWrex (nb088AlphaDummy046 u A B R)
            (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
            (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
              (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_051`. -/
@[expose]
noncomputable def nb088AlphaDummy051 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy041 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_052`. -/
@[expose]
noncomputable def nb088AlphaDummy052 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy042 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_053`. -/
@[expose]
noncomputable def nb088AlphaDummy053 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy044 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_054`. -/
@[expose]
noncomputable def nb088AlphaDummy054 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy044 A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_055`. -/
@[expose]
noncomputable def nb088AlphaDummy055 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy046 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_056`. -/
@[expose]
noncomputable def nb088AlphaDummy056 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy046 u A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_057`. -/
@[expose]
noncomputable def nb088AlphaDummy057 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb088AlphaDummy053 A B C R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb088AlphaDummy053 A B C R)) (synC1c))).fv ∪
      ((Class.cv (nb088AlphaDummy053 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_058`. -/
@[expose]
noncomputable def nb088AlphaDummy058 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb088AlphaDummy055 u A B R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb088AlphaDummy055 u A B R)) (synC1c))).fv ∪
      ((Class.cv (nb088AlphaDummy055 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_059`. -/
@[expose]
noncomputable def nb088AlphaDummy059 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_060`. -/
@[expose]
noncomputable def nb088AlphaDummy060 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_061`. -/
@[expose]
noncomputable def nb088AlphaDummy061 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_062`. -/
@[expose]
noncomputable def nb088AlphaDummy062 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_063`. -/
@[expose]
noncomputable def nb088AlphaDummy063 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_064`. -/
@[expose]
noncomputable def nb088AlphaDummy064 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_065`. -/
@[expose]
noncomputable def nb088AlphaDummy065 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
          (Class.cv (nb088AlphaDummy061 A B C R)))).fv ∪
      ((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
          (Class.cv (nb088AlphaDummy061 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_066`. -/
@[expose]
noncomputable def nb088AlphaDummy066 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
          (Class.cv (nb088AlphaDummy064 u A B R)))).fv ∪
      ((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
          (Class.cv (nb088AlphaDummy064 u A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_067`. -/
@[expose]
noncomputable def nb088AlphaDummy067 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy061 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_068`. -/
@[expose]
noncomputable def nb088AlphaDummy068 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
      ((Class.cv (nb088AlphaDummy064 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_069`. -/
@[expose]
noncomputable def nb088AlphaDummy069 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb088AlphaDummy060 A B C R)))).fv ∪
      ((synCcompl (Class.cv (nb088AlphaDummy061 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_070`. -/
@[expose]
noncomputable def nb088AlphaDummy070 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb088AlphaDummy063 u A B R)))).fv ∪
      ((synCcompl (Class.cv (nb088AlphaDummy064 u A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_071`. -/
@[expose]
noncomputable def nb088AlphaDummy071 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy060 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_072`. -/
@[expose]
noncomputable def nb088AlphaDummy072 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
      ((Class.cv (nb088AlphaDummy063 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_073`. -/
@[expose]
noncomputable def nb088AlphaDummy073 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy061 A B C R))).fv ∪
      ((Class.cv (nb088AlphaDummy061 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_074`. -/
@[expose]
noncomputable def nb088AlphaDummy074 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb088AlphaDummy064 u A B R))).fv ∪
      ((Class.cv (nb088AlphaDummy064 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_075`. -/
@[expose]
noncomputable def nb088AlphaDummy075 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb088AlphaDummy043 A B C R)
          (synWrex (nb088AlphaDummy044 A B C R) (Class.cv (nb088AlphaDummy000 A B C R))
            (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
              (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy043 A B C R)
          (synWrex (nb088AlphaDummy044 A B C R) (Class.cv (nb088AlphaDummy000 A B C R))
            (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
              (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_076`. -/
@[expose]
noncomputable def nb088AlphaDummy076 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb088AlphaDummy045 u A B R)
          (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
              (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy045 u A B R)
          (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
              (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_077`. -/
@[expose]
noncomputable def nb088AlphaDummy077 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_078`. -/
@[expose]
noncomputable def nb088AlphaDummy078 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_079`. -/
@[expose]
noncomputable def nb088AlphaDummy079 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb088AlphaDummy044 A B C R)))).fv ∪
      ((synCphi (Class.cv (nb088AlphaDummy044 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb088_alpha_dummy_080`. -/
@[expose]
noncomputable def nb088AlphaDummy080 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb088AlphaDummy046 u A B R)))).fv ∪
      ((synCphi (Class.cv (nb088AlphaDummy046 u A B R)))).fv) 0)

theorem nb088_fresh_000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy011 A B C R) ∉
      (((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))))).fv) :=
  by
  simpa only [nb088AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))))).fv)
      0

theorem nb088_fresh_001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy035 A B C R) ∉
      (((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy005 A B C R)
            (synWrex (nb088AlphaDummy006 A B C R) (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb088AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy005 A B C R)
            (synWrex (nb088AlphaDummy006 A B C R) (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb088_fresh_002 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy036 u A B C R) ∉
      (((Class.cab (nb088AlphaDummy007 u A B C R) (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb088AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb088AlphaDummy007 u A B C R) (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb088_fresh_003 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy012 u A B C R) ∉
      (((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))))).fv) :=
  by
  simpa only [nb088AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))))).fv)
      0

theorem nb088_fresh_004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy075 A B C R) ∉
      (((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy043 A B C R)
            (synWrex (nb088AlphaDummy044 A B C R) (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb088AlphaDummy075] using
    freshVar_not_mem
      (((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy043 A B C R)
            (synWrex (nb088AlphaDummy044 A B C R) (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb088_fresh_005 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy049 A B C R) ∉
      (((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))))).fv) :=
  by
  simpa only [nb088AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))))).fv)
      0

theorem nb088_fresh_006 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy076 u A B R) ∉
      (((Class.cab (nb088AlphaDummy045 u A B R)
            (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy045 u A B R)
            (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb088AlphaDummy076] using
    freshVar_not_mem
      (((Class.cab (nb088AlphaDummy045 u A B R)
            (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy045 u A B R)
            (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb088_fresh_007 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy050 u A B R) ∉
      (((Class.cab (nb088AlphaDummy045 u A B R) (synWrex (nb088AlphaDummy046 u A B R)
              (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy045 u A B R) (synWrex (nb088AlphaDummy046 u A B R)
              (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))))).fv) :=
  by
  simpa only [nb088AlphaDummy050] using
    freshVar_not_mem
      (((Class.cab (nb088AlphaDummy045 u A B R) (synWrex (nb088AlphaDummy046 u A B R)
              (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy045 u A B R) (synWrex (nb088AlphaDummy046 u A B R)
              (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))))).fv)
      0

theorem nb088_fresh_008 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy005 A B C R) ∉
      (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy001 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy001 A B C R))).fv)
      0

theorem nb088_fresh_009 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy006 A B C R) ∉
      (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy001 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy001 A B C R))).fv)
      1

theorem nb088_distinct_010 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy005 A B C R) ≠ (nb088AlphaDummy006 A B C R) := by
  simpa only [nb088AlphaDummy005, nb088AlphaDummy006] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy001 A B C R))).fv) (i := 0) (j := 1) (by decide))

theorem nb088_fresh_011 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy013 A B C R) ∉ (((Class.cv (nb088AlphaDummy006 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy006 A B C R))).fv) 0

theorem nb088_fresh_012 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy014 A B C R) ∉ (((Class.cv (nb088AlphaDummy006 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy006 A B C R))).fv) 1

theorem nb088_distinct_013 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy013 A B C R) ≠ (nb088AlphaDummy014 A B C R) := by
  simpa only [nb088AlphaDummy013, nb088AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy006 A B C R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb088_fresh_014 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy015 u A B C R) ∉
      (((Class.cv (nb088AlphaDummy008 u A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy008 u A B C R))).fv) 0

theorem nb088_fresh_015 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy016 u A B C R) ∉
      (((Class.cv (nb088AlphaDummy008 u A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy008 u A B C R))).fv) 1

theorem nb088_distinct_016 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy016 u A B C R) := by
  simpa only [nb088AlphaDummy015, nb088AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy008 u A B C R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb088_fresh_017 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy019 A B C R) ∉
      (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) 0

theorem nb088_fresh_018 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy020 A B C R) ∉
      (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) 1

theorem nb088_fresh_019 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy021 A B C R) ∉
      (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) 2

theorem nb088_distinct_020 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy019 A B C R) ≠ (nb088AlphaDummy020 A B C R) := by
  simpa only [nb088AlphaDummy019, nb088AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb088_distinct_021 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy019 A B C R) ≠ (nb088AlphaDummy021 A B C R) := by
  simpa only [nb088AlphaDummy019, nb088AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb088_distinct_022 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy021 A B C R) := by
  simpa only [nb088AlphaDummy020, nb088AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb088_fresh_023 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy022 u A B C R) ∉
      (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv)
      0

theorem nb088_fresh_024 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy023 u A B C R) ∉
      (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv)
      1

theorem nb088_fresh_025 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy024 u A B C R) ∉
      (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv)
      2

theorem nb088_distinct_026 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy022 u A B C R) ≠ (nb088AlphaDummy023 u A B C R) := by
  simpa only [nb088AlphaDummy022, nb088AlphaDummy023] using
    (freshVar_injective
      (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb088_distinct_027 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy022 u A B C R) ≠ (nb088AlphaDummy024 u A B C R) := by
  simpa only [nb088AlphaDummy022, nb088AlphaDummy024] using
    (freshVar_injective
      (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) (i := 0) (j :=
      2) (by decide))

theorem nb088_distinct_028 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy024 u A B C R) := by
  simpa only [nb088AlphaDummy023, nb088AlphaDummy024] using
    (freshVar_injective
      (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) (i := 1) (j :=
      2) (by decide))

theorem nb088_fresh_029 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy031 A B C R) ∉
      (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy020 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy020 A B C R))).fv)
      0

theorem nb088_fresh_030 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy027 A B C R) ∉
      (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy021 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy021 A B C R))).fv)
      0

theorem nb088_fresh_031 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy033 A B C R) ∉
      (((Class.cv (nb088AlphaDummy021 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy021 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy021 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy021 A B C R))).fv)
      0

theorem nb088_fresh_032 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy032 u A B C R) ∉
      (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy023 u A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy023 u A B C R))).fv)
      0

theorem nb088_fresh_033 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy028 u A B C R) ∉
      (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy024 u A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy024 u A B C R))).fv)
      0

theorem nb088_fresh_034 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy034 u A B C R) ∉
      (((Class.cv (nb088AlphaDummy024 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy024 u A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy024 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy024 u A B C R))).fv)
      0

theorem nb088_fresh_035 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy051 A B C R) ∉ (((Class.cv (nb088AlphaDummy041 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy041 A B C R))).fv) 0

theorem nb088_fresh_036 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy052 u A B R) ∉ (((Class.cv (nb088AlphaDummy042 u A B R))).fv) :=
  by
  simpa only [nb088AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy042 u A B R))).fv) 0

theorem nb088_fresh_037 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy053 A B C R) ∉ (((Class.cv (nb088AlphaDummy044 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy044 A B C R))).fv) 0

theorem nb088_fresh_038 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy054 A B C R) ∉ (((Class.cv (nb088AlphaDummy044 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy054] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy044 A B C R))).fv) 1

theorem nb088_distinct_039 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy053 A B C R) ≠ (nb088AlphaDummy054 A B C R) := by
  simpa only [nb088AlphaDummy053, nb088AlphaDummy054] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy044 A B C R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb088_fresh_040 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy055 u A B R) ∉ (((Class.cv (nb088AlphaDummy046 u A B R))).fv) :=
  by
  simpa only [nb088AlphaDummy055] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy046 u A B R))).fv) 0

theorem nb088_fresh_041 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy056 u A B R) ∉ (((Class.cv (nb088AlphaDummy046 u A B R))).fv) :=
  by
  simpa only [nb088AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy046 u A B R))).fv) 1

theorem nb088_distinct_042 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy055 u A B R) ≠ (nb088AlphaDummy056 u A B R) := by
  simpa only [nb088AlphaDummy055, nb088AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy046 u A B R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb088_fresh_043 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy059 A B C R) ∉
      (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) 0

theorem nb088_fresh_044 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy060 A B C R) ∉
      (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) 1

theorem nb088_fresh_045 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy061 A B C R) ∉
      (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) 2

theorem nb088_distinct_046 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy059 A B C R) ≠ (nb088AlphaDummy060 A B C R) := by
  simpa only [nb088AlphaDummy059, nb088AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb088_distinct_047 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy059 A B C R) ≠ (nb088AlphaDummy061 A B C R) := by
  simpa only [nb088AlphaDummy059, nb088AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb088_distinct_048 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy060 A B C R) ≠ (nb088AlphaDummy061 A B C R) := by
  simpa only [nb088AlphaDummy060, nb088AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb088_fresh_049 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy062 u A B R) ∉
      (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) 0

theorem nb088_fresh_050 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy063 u A B R) ∉
      (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) 1

theorem nb088_fresh_051 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy064 u A B R) ∉
      (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb088AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) 2

theorem nb088_distinct_052 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy062 u A B R) ≠ (nb088AlphaDummy063 u A B R) := by
  simpa only [nb088AlphaDummy062, nb088AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb088_distinct_053 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy062 u A B R) ≠ (nb088AlphaDummy064 u A B R) := by
  simpa only [nb088AlphaDummy062, nb088AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb088_distinct_054 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy063 u A B R) ≠ (nb088AlphaDummy064 u A B R) := by
  simpa only [nb088AlphaDummy063, nb088AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb088_fresh_055 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy071 A B C R) ∉
      (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy060 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy060 A B C R))).fv)
      0

theorem nb088_fresh_056 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy067 A B C R) ∉
      (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy061 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy061 A B C R))).fv)
      0

theorem nb088_fresh_057 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy073 A B C R) ∉
      (((Class.cv (nb088AlphaDummy061 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy061 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy073] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy061 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy061 A B C R))).fv)
      0

theorem nb088_fresh_058 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy072 u A B R) ∉
      (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy063 u A B R))).fv) :=
  by
  simpa only [nb088AlphaDummy072] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy063 u A B R))).fv)
      0

theorem nb088_fresh_059 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy068 u A B R) ∉
      (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy064 u A B R))).fv) :=
  by
  simpa only [nb088AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy064 u A B R))).fv)
      0

theorem nb088_fresh_060 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy074 u A B R) ∉
      (((Class.cv (nb088AlphaDummy064 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy064 u A B R))).fv) :=
  by
  simpa only [nb088AlphaDummy074] using
    freshVar_not_mem
      (((Class.cv (nb088AlphaDummy064 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy064 u A B R))).fv)
      0

theorem nb088_fresh_061 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy007 u A B C R) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) 0

theorem nb088_fresh_062 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy008 u A B C R) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy008] using
    freshVar_not_mem
      (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) 1

theorem nb088_distinct_063 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy007 u A B C R) ≠ (nb088AlphaDummy008 u A B C R) := by
  simpa only [nb088AlphaDummy007, nb088AlphaDummy008] using
    (freshVar_injective
      (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb088_fresh_064 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy017 A B C R) ∉
      (((Wff.classMem (Class.cv (nb088AlphaDummy013 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy013 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy013 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb088AlphaDummy013 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy013 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy013 A B C R))).fv)
      0

theorem nb088_fresh_065 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy018 u A B C R) ∉
      (((Wff.classMem (Class.cv (nb088AlphaDummy015 u A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy015 u A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy015 u A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb088AlphaDummy015 u A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy015 u A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy015 u A B C R))).fv)
      0

theorem nb088_fresh_066 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy057 A B C R) ∉
      (((Wff.classMem (Class.cv (nb088AlphaDummy053 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy053 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy053 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy057] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb088AlphaDummy053 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy053 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy053 A B C R))).fv)
      0

theorem nb088_fresh_067 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy058 u A B R) ∉
      (((Wff.classMem (Class.cv (nb088AlphaDummy055 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy055 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy055 u A B R))).fv) :=
  by
  simpa only [nb088AlphaDummy058] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb088AlphaDummy055 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy055 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy055 u A B R))).fv)
      0

theorem nb088_fresh_068 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy009 A B C R) ∉
      (((synCcompl (Class.cab (nb088AlphaDummy005 A B C R)
              (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb088AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb088AlphaDummy005 A B C R)
              (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                    (synCsn (synC0c)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR5H088P001Part002`. -/


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

theorem nb088_fresh_069 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy010 u A B C R) ∉
      (((synCcompl (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R)
                (Class.cv (nb088AlphaDummy002 u A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb088AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R)
                (Class.cv (nb088AlphaDummy002 u A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb088_fresh_070 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy047 A B C R) ∉
      (((synCcompl (Class.cab (nb088AlphaDummy043 A B C R)
              (synWrex (nb088AlphaDummy044 A B C R)
                (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
                (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
                (Class.cv (nb088AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb088AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb088AlphaDummy043 A B C R)
              (synWrex (nb088AlphaDummy044 A B C R)
                (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
                (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
                (Class.cv (nb088AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb088_fresh_071 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy048 u A B R) ∉
      (((synCcompl (Class.cab (nb088AlphaDummy045 u A B R)
              (synWrex (nb088AlphaDummy046 u A B R)
                (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
                (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                  (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy045 u A B R)
              (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb088AlphaDummy048] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb088AlphaDummy045 u A B R)
              (synWrex (nb088AlphaDummy046 u A B R)
                (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
                (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                  (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy045 u A B R)
              (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb088_fresh_072 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy029 A B C R) ∉
      (((synCcompl (Class.cv (nb088AlphaDummy020 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy021 A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb088AlphaDummy020 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy021 A B C R)))).fv)
      0

theorem nb088_fresh_073 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy030 u A B C R) ∉
      (((synCcompl (Class.cv (nb088AlphaDummy023 u A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy024 u A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb088AlphaDummy023 u A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy024 u A B C R)))).fv)
      0

theorem nb088_fresh_074 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy069 A B C R) ∉
      (((synCcompl (Class.cv (nb088AlphaDummy060 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy061 A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy069] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb088AlphaDummy060 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy061 A B C R)))).fv)
      0

theorem nb088_fresh_075 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy070 u A B R) ∉
      (((synCcompl (Class.cv (nb088AlphaDummy063 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy064 u A B R)))).fv) :=
  by
  simpa only [nb088AlphaDummy070] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb088AlphaDummy063 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy064 u A B R)))).fv)
      0

theorem nb088_fresh_076 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy037 A B C R) ∉
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb088AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb088_fresh_077 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy038 u A B C R) ∉
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb088AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb088_fresh_078 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy077 A B C R) ∉
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb088AlphaDummy077] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb088_fresh_079 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy078 u A B R) ∉
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb088AlphaDummy078] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb088_fresh_080 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy025 A B C R) ∉
      (((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
            (Class.cv (nb088AlphaDummy021 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
            (Class.cv (nb088AlphaDummy021 A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
            (Class.cv (nb088AlphaDummy021 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
            (Class.cv (nb088AlphaDummy021 A B C R)))).fv)
      0

theorem nb088_fresh_081 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy026 u A B C R) ∉
      (((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
            (Class.cv (nb088AlphaDummy024 u A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
            (Class.cv (nb088AlphaDummy024 u A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
            (Class.cv (nb088AlphaDummy024 u A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
            (Class.cv (nb088AlphaDummy024 u A B C R)))).fv)
      0

theorem nb088_fresh_082 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy065 A B C R) ∉
      (((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
            (Class.cv (nb088AlphaDummy061 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
            (Class.cv (nb088AlphaDummy061 A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy065] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
            (Class.cv (nb088AlphaDummy061 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
            (Class.cv (nb088AlphaDummy061 A B C R)))).fv)
      0

theorem nb088_fresh_083 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy066 u A B R) ∉
      (((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
            (Class.cv (nb088AlphaDummy064 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
            (Class.cv (nb088AlphaDummy064 u A B R)))).fv) :=
  by
  simpa only [nb088AlphaDummy066] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
            (Class.cv (nb088AlphaDummy064 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
            (Class.cv (nb088AlphaDummy064 u A B R)))).fv)
      0

theorem nb088_fresh_084 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy039 A B C R) ∉
      (((synCphi (Class.cv (nb088AlphaDummy006 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy006 A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb088AlphaDummy006 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy006 A B C R)))).fv)
      0

theorem nb088_fresh_085 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy040 u A B C R) ∉
      (((synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))).fv)
      0

theorem nb088_fresh_086 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy079 A B C R) ∉
      (((synCphi (Class.cv (nb088AlphaDummy044 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy044 A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy079] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb088AlphaDummy044 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy044 A B C R)))).fv)
      0

theorem nb088_fresh_087 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy080 u A B R) ∉
      (((synCphi (Class.cv (nb088AlphaDummy046 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy046 u A B R)))).fv) :=
  by
  simpa only [nb088AlphaDummy080] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb088AlphaDummy046 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy046 u A B R)))).fv)
      0

theorem nb088_fresh_088 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy043 A B C R) ∉
      (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
        ((Class.cv (nb088AlphaDummy000 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy043] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
        ((Class.cv (nb088AlphaDummy000 A B C R))).fv)
      0

theorem nb088_fresh_089 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy044 A B C R) ∉
      (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
        ((Class.cv (nb088AlphaDummy000 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy044] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
        ((Class.cv (nb088AlphaDummy000 A B C R))).fv)
      1

theorem nb088_distinct_090 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy043 A B C R) ≠ (nb088AlphaDummy044 A B C R) := by
  simpa only [nb088AlphaDummy043, nb088AlphaDummy044] using
    (freshVar_injective (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
        ((Class.cv (nb088AlphaDummy000 A B C R))).fv) (i := 0) (j := 1) (by decide))

theorem nb088_fresh_091 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy045 u A B R) ∉
      (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  simpa only [nb088AlphaDummy045] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv) 0

theorem nb088_fresh_092 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy046 u A B R) ∉
      (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  simpa only [nb088AlphaDummy046] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv) 1

theorem nb088_distinct_093 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy045 u A B R) ≠ (nb088AlphaDummy046 u A B R) := by
  simpa only [nb088AlphaDummy045, nb088AlphaDummy046] using
    (freshVar_injective
      (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb088_fresh_094 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy041 A B C R) ∉
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088AlphaDummy000 A B C R))).fv) :=
  by
  simpa only [nb088AlphaDummy041] using
    freshVar_not_mem
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088AlphaDummy000 A B C R))).fv) 0

theorem nb088_fresh_095 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy042 u A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb088AlphaDummy042] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0

theorem nb088_fresh_096 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb088AlphaDummy000] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb088_fresh_097 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy001 A B C R) ∉
      (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪ ((synCpw1 (synCpw1 C))).fv ∪
        ((synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))).fv) :=
  by
  simpa only [nb088AlphaDummy001] using
    freshVar_not_mem
      (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪ ((synCpw1 (synCpw1 C))).fv ∪
        ((synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))).fv)
      0

theorem nb088_fresh_098 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy003 A B C R) ∉
      (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪
          ({(nb088AlphaDummy001 A B C R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb088AlphaDummy000 A B C R)) (synCpw1 (synCpw1 C)))
            (Wff.classEq (Class.cv (nb088AlphaDummy001 A B C R))
              (synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))))).fv) :=
  by
  simpa only [nb088AlphaDummy003] using
    freshVar_not_mem
      (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪
          ({(nb088AlphaDummy001 A B C R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb088AlphaDummy000 A B C R)) (synCpw1 (synCpw1 C)))
            (Wff.classEq (Class.cv (nb088AlphaDummy001 A B C R))
              (synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))))).fv)
      0

theorem nb088_fresh_099 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy002 u A B C R) ∉
      (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 C))).fv ∪
        ((synCfdrowfib R A B (Class.cv u))).fv) :=
  by
  simpa only [nb088AlphaDummy002] using
    freshVar_not_mem
      (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 C))).fv ∪
        ((synCfdrowfib R A B (Class.cv u))).fv)
      0

theorem nb088_fresh_100 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy004 u A B C R) ∉
      (({ u } : Finset Var) ∪ ({(nb088AlphaDummy002 u A B C R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 C)))
            (Wff.classEq (Class.cv (nb088AlphaDummy002 u A B C R))
              (synCfdrowfib R A B (Class.cv u))))).fv) :=
  by
  simpa only [nb088AlphaDummy004] using
    freshVar_not_mem
      (({ u } : Finset Var) ∪ ({(nb088AlphaDummy002 u A B C R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 C)))
            (Wff.classEq (Class.cv (nb088AlphaDummy002 u A B C R))
              (synCfdrowfib R A B (Class.cv u))))).fv)
      0

theorem nb088_support_mem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪
          ({(nb088AlphaDummy001 A B C R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb088AlphaDummy000 A B C R)) (synCpw1 (synCpw1 C)))
            (Wff.classEq (Class.cv (nb088AlphaDummy001 A B C R))
              (synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0001 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    u ∈
      (({ u } : Finset Var) ∪ ({(nb088AlphaDummy002 u A B C R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 C)))
            (Wff.classEq (Class.cv (nb088AlphaDummy002 u A B C R))
              (synCfdrowfib R A B (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy001 A B C R) ∈
      (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪
          ({(nb088AlphaDummy001 A B C R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb088AlphaDummy000 A B C R)) (synCpw1 (synCpw1 C)))
            (Wff.classEq (Class.cv (nb088AlphaDummy001 A B C R))
              (synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0003 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy002 u A B C R) ∈
      (({ u } : Finset Var) ∪ ({(nb088AlphaDummy002 u A B C R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 C)))
            (Wff.classEq (Class.cv (nb088AlphaDummy002 u A B C R))
              (synCfdrowfib R A B (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      (({(nb088AlphaDummy000 A B C R)} : Finset Var) ∪ ((synCpw1 (synCpw1 C))).fv ∪
        ((synCfdrowfib R A B (Class.cv (nb088AlphaDummy000 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0005 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    u ∈
      (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 C))).fv ∪
        ((synCfdrowfib R A B (Class.cv u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy001 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0007 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      (((synCcompl (Class.cab (nb088AlphaDummy005 A B C R)
              (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy000 A B C R) ≠ (nb088AlphaDummy005 A B C R) from (by
          unfold nb088AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy000 A B C R) ≠ (nb088AlphaDummy006 A B C R) from (by
            unfold nb088AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0008 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0009 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    u ∈
      (((synCcompl (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R)
                (Class.cv (nb088AlphaDummy002 u A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb088AlphaDummy007 u A B C R) from (by
          unfold nb088AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb088AlphaDummy008 u A B C R) from (by
            unfold nb088AlphaDummy008;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0010 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      (((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy000 A B C R) ≠ (nb088AlphaDummy005 A B C R) from (by
          unfold nb088AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy000 A B C R) ≠ (nb088AlphaDummy006 A B C R) from (by
            unfold nb088AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0011 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    u ∈
      (((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb088AlphaDummy007 u A B C R) from (by
          unfold nb088AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb088AlphaDummy008 u A B C R) from (by
            unfold nb088AlphaDummy008;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0012 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy006 A B C R) ∈ (((Class.cv (nb088AlphaDummy006 A B C R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0013 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy008 u A B C R) ∈
      (((Class.cv (nb088AlphaDummy008 u A B C R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0014 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy013 A B C R) ∈
      (((Wff.classMem (Class.cv (nb088AlphaDummy013 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy013 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy013 A B C R))).fv) :=
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

theorem nb088_support_mem_0015 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy015 u A B C R) ∈
      (((Wff.classMem (Class.cv (nb088AlphaDummy015 u A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy015 u A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy015 u A B C R))).fv) :=
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

theorem nb088_support_mem_0016 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy013 A B C R) ∈
      (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0017 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy015 u A B C R) ∈
      (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0018 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy020 A B C R) ∈
      (((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
            (Class.cv (nb088AlphaDummy021 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
            (Class.cv (nb088AlphaDummy021 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0019 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy023 u A B C R) ∈
      (((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
            (Class.cv (nb088AlphaDummy024 u A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
            (Class.cv (nb088AlphaDummy024 u A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0020 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy020 A B C R) ∈
      (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy021 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0021 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy023 u A B C R) ∈
      (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy024 u A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0022 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy021 A B C R) ∈
      (((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
            (Class.cv (nb088AlphaDummy021 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy020 A B C R))
            (Class.cv (nb088AlphaDummy021 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0023 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy024 u A B C R) ∈
      (((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
            (Class.cv (nb088AlphaDummy024 u A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy023 u A B C R))
            (Class.cv (nb088AlphaDummy024 u A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0024 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy021 A B C R) ∈
      (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy021 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0025 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy024 u A B C R) ∈
      (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy024 u A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0026 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy020 A B C R) ∈
      (((synCcompl (Class.cv (nb088AlphaDummy020 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy021 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0027 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy023 u A B C R) ∈
      (((synCcompl (Class.cv (nb088AlphaDummy023 u A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy024 u A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0028 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy020 A B C R) ∈
      (((Class.cv (nb088AlphaDummy020 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy020 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0029 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy023 u A B C R) ∈
      (((Class.cv (nb088AlphaDummy023 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy023 u A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0030 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy021 A B C R) ∈
      (((synCcompl (Class.cv (nb088AlphaDummy020 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy021 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0031 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy024 u A B C R) ∈
      (((synCcompl (Class.cv (nb088AlphaDummy023 u A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy024 u A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0032 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy021 A B C R) ∈
      (((Class.cv (nb088AlphaDummy021 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy021 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0033 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy024 u A B C R) ∈
      (((Class.cv (nb088AlphaDummy024 u A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy024 u A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0034 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy001 A B C R) ∈
      (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy001 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0035 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy001 A B C R) ∈
      (((synCcompl (Class.cab (nb088AlphaDummy005 A B C R)
              (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy005 A B C R) from (by
          unfold nb088AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy006 A B C R) from (by
            unfold nb088AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0036 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy002 u A B C R) ∈
      (((Class.cv u)).fv ∪ ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0037 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy002 u A B C R) ∈
      (((synCcompl (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R) (Class.cv u)
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R)
                (Class.cv (nb088AlphaDummy002 u A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy007 u A B C R) from (by
          unfold nb088AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy008 u A B C R) from (by
            unfold nb088AlphaDummy008;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0038 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy001 A B C R) ∈
      (((Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy005 A B C R)
            (synWrex (nb088AlphaDummy006 A B C R) (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy005 A B C R) from (by
          unfold nb088AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy006 A B C R) from (by
            unfold nb088AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0039 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy002 u A B C R) ∈
      (((Class.cab (nb088AlphaDummy007 u A B C R) (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy007 u A B C R) from (by
          unfold nb088AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy008 u A B C R) from (by
            unfold nb088AlphaDummy008;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0040 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy006 A B C R) ∈
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy006 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0041 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy008 u A B C R) ∈
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy008 u A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0042 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy006 A B C R) ∈
      (((synCphi (Class.cv (nb088AlphaDummy006 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy006 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0043 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy008 u A B C R) ∈
      (((synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0044 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy041 A B C R) ∈
      (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
        ((Class.cv (nb088AlphaDummy000 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0045 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy041 A B C R) ∈
      (((synCcompl (Class.cab (nb088AlphaDummy043 A B C R)
              (synWrex (nb088AlphaDummy044 A B C R)
                (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
                (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
                (Class.cv (nb088AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy041 A B C R) ≠ (nb088AlphaDummy043 A B C R) from (by
          unfold nb088AlphaDummy043;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0044 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy041 A B C R) ≠ (nb088AlphaDummy044 A B C R) from (by
            unfold nb088AlphaDummy044;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0044 A B C R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0046 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy042 u A B R) ∈
      (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0047 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy042 u A B R) ∈
      (((synCcompl (Class.cab (nb088AlphaDummy045 u A B R)
              (synWrex (nb088AlphaDummy046 u A B R)
                (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
                (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                  (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy045 u A B R)
              (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy042 u A B R) ≠ (nb088AlphaDummy045 u A B R) from (by
          unfold nb088AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0046 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy042 u A B R) ≠ (nb088AlphaDummy046 u A B R) from (by
            unfold nb088AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0046 u A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0048 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy041 A B C R) ∈
      (((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy041 A B C R) ≠ (nb088AlphaDummy043 A B C R) from (by
          unfold nb088AlphaDummy043;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0044 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy041 A B C R) ≠ (nb088AlphaDummy044 A B C R) from (by
            unfold nb088AlphaDummy044;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0044 A B C R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0049 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy042 u A B R) ∈
      (((Class.cab (nb088AlphaDummy045 u A B R) (synWrex (nb088AlphaDummy046 u A B R)
              (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))))).fv ∪
        ((Class.cab (nb088AlphaDummy045 u A B R) (synWrex (nb088AlphaDummy046 u A B R)
              (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy042 u A B R) ≠ (nb088AlphaDummy045 u A B R) from (by
          unfold nb088AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0046 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy042 u A B R) ≠ (nb088AlphaDummy046 u A B R) from (by
            unfold nb088AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0046 u A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0050 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy041 A B C R) ∈ (((Class.cv (nb088AlphaDummy041 A B C R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0051 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy042 u A B R) ∈ (((Class.cv (nb088AlphaDummy042 u A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0052 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy044 A B C R) ∈ (((Class.cv (nb088AlphaDummy044 A B C R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0053 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy046 u A B R) ∈ (((Class.cv (nb088AlphaDummy046 u A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0054 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy053 A B C R) ∈
      (((Wff.classMem (Class.cv (nb088AlphaDummy053 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy053 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy053 A B C R))).fv) :=
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

theorem nb088_support_mem_0055 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy055 u A B R) ∈
      (((Wff.classMem (Class.cv (nb088AlphaDummy055 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb088AlphaDummy055 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb088AlphaDummy055 u A B R))).fv) :=
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

theorem nb088_support_mem_0056 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy053 A B C R) ∈
      (((Class.cv (nb088AlphaDummy053 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0057 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy055 u A B R) ∈
      (((Class.cv (nb088AlphaDummy055 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0058 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy060 A B C R) ∈
      (((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
            (Class.cv (nb088AlphaDummy061 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
            (Class.cv (nb088AlphaDummy061 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0059 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy063 u A B R) ∈
      (((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
            (Class.cv (nb088AlphaDummy064 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
            (Class.cv (nb088AlphaDummy064 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0060 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy060 A B C R) ∈
      (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy061 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0061 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy063 u A B R) ∈
      (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy064 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0062 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy061 A B C R) ∈
      (((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
            (Class.cv (nb088AlphaDummy061 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy060 A B C R))
            (Class.cv (nb088AlphaDummy061 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0063 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy064 u A B R) ∈
      (((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
            (Class.cv (nb088AlphaDummy064 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb088AlphaDummy063 u A B R))
            (Class.cv (nb088AlphaDummy064 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0064 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy061 A B C R) ∈
      (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy061 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0065 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy064 u A B R) ∈
      (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy064 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0066 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy060 A B C R) ∈
      (((synCcompl (Class.cv (nb088AlphaDummy060 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy061 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0067 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy063 u A B R) ∈
      (((synCcompl (Class.cv (nb088AlphaDummy063 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy064 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0068 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy060 A B C R) ∈
      (((Class.cv (nb088AlphaDummy060 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy060 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0069 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy063 u A B R) ∈
      (((Class.cv (nb088AlphaDummy063 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy063 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0070 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy061 A B C R) ∈
      (((synCcompl (Class.cv (nb088AlphaDummy060 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy061 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0071 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy064 u A B R) ∈
      (((synCcompl (Class.cv (nb088AlphaDummy063 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb088AlphaDummy064 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0072 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy061 A B C R) ∈
      (((Class.cv (nb088AlphaDummy061 A B C R))).fv ∪
        ((Class.cv (nb088AlphaDummy061 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0073 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy064 u A B R) ∈
      (((Class.cv (nb088AlphaDummy064 u A B R))).fv ∪
        ((Class.cv (nb088AlphaDummy064 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0074 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088AlphaDummy000 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0075 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0076 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      (((synCsn (Class.cv (nb088AlphaDummy041 A B C R)))).fv ∪
        ((Class.cv (nb088AlphaDummy000 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0077 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      (((synCcompl (Class.cab (nb088AlphaDummy043 A B C R)
              (synWrex (nb088AlphaDummy044 A B C R)
                (synCsn (Class.cv (nb088AlphaDummy041 A B C R)))
                (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                  (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
                (Class.cv (nb088AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy000 A B C R) ≠ (nb088AlphaDummy043 A B C R) from (by
          unfold nb088AlphaDummy043;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy000 A B C R) ≠ (nb088AlphaDummy044 A B C R) from (by
            unfold nb088AlphaDummy044;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0078 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈ (((synCsn (Class.cv (nb088AlphaDummy042 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0079 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((synCcompl (Class.cab (nb088AlphaDummy045 u A B R)
              (synWrex (nb088AlphaDummy046 u A B R)
                (synCsn (Class.cv (nb088AlphaDummy042 u A B R)))
                (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                  (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb088AlphaDummy045 u A B R)
              (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb088AlphaDummy045 u A B R) from (by
          unfold nb088AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb088AlphaDummy046 u A B R) from (by
            unfold nb088AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0080 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy000 A B C R) ∈
      (((Class.cab (nb088AlphaDummy043 A B C R) (synWrex (nb088AlphaDummy044 A B C R)
              (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy043 A B C R)
            (synWrex (nb088AlphaDummy044 A B C R) (Class.cv (nb088AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy043 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy044 A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb088AlphaDummy000 A B C R) ≠ (nb088AlphaDummy043 A B C R) from (by
          unfold nb088AlphaDummy043;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb088AlphaDummy000 A B C R) ≠ (nb088AlphaDummy044 A B C R) from (by
            unfold nb088AlphaDummy044;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0081 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((Class.cab (nb088AlphaDummy045 u A B R)
            (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb088AlphaDummy045 u A B R)
            (synWrex (nb088AlphaDummy046 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb088AlphaDummy045 u A B R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy046 u A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb088AlphaDummy045 u A B R) from (by
          unfold nb088AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb088AlphaDummy046 u A B R) from (by
            unfold nb088AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0082 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy044 A B C R) ∈
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy044 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0083 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy046 u A B R) ∈
      (((synCcompl (synCphi (Class.cv (nb088AlphaDummy046 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0084 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088AlphaDummy044 A B C R) ∈
      (((synCphi (Class.cv (nb088AlphaDummy044 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy044 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0085 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088AlphaDummy046 u A B R) ∈
      (((synCphi (Class.cv (nb088AlphaDummy046 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb088AlphaDummy046 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
