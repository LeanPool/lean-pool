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

/-! Certificates from `NAR4C087C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_000`. -/
@[expose]
noncomputable def nb087AlphaDummy000 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_001`. -/
@[expose]
noncomputable def nb087AlphaDummy001 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_002`. -/
@[expose]
noncomputable def nb087AlphaDummy002 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_003`. -/
@[expose]
noncomputable def nb087AlphaDummy003 (C : Class) (d : Var) : Var :=
  (freshVar (((synCsn (Class.cv d))).fv ∪ (C).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_004`. -/
@[expose]
noncomputable def nb087AlphaDummy004 (C : Class) (d : Var) : Var :=
  (freshVar (((synCsn (Class.cv d))).fv ∪ (C).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_005`. -/
@[expose]
noncomputable def nb087AlphaDummy005 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb087AlphaDummy001 A B C R)
            (synWrex (nb087AlphaDummy002 A B C R)
              (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R) C
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_006`. -/
@[expose]
noncomputable def nb087AlphaDummy006 (C : Class) (d : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCphi (Class.cv (nb087AlphaDummy004 C d)))))))).fv ∪ ((synCcompl
          (Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_007`. -/
@[expose]
noncomputable def nb087AlphaDummy007 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb087AlphaDummy001 A B C R)
          (synWrex (nb087AlphaDummy002 A B C R)
            (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
            (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
              (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))))).fv ∪
      ((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R)
            (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
            (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
              (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_008`. -/
@[expose]
noncomputable def nb087AlphaDummy008 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cab (nb087AlphaDummy003 C d)
          (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
            (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
              (synCphi (Class.cv (nb087AlphaDummy004 C d))))))).fv ∪
      ((Class.cab (nb087AlphaDummy003 C d)
          (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
            (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
              (synCphi (Class.cv (nb087AlphaDummy004 C d))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_009`. -/
@[expose]
noncomputable def nb087AlphaDummy009 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy000 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_010`. -/
@[expose]
noncomputable def nb087AlphaDummy010 (d : Var) : Var :=
  (freshVar (((Class.cv d)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_011`. -/
@[expose]
noncomputable def nb087AlphaDummy011 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy002 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_012`. -/
@[expose]
noncomputable def nb087AlphaDummy012 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy002 A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_013`. -/
@[expose]
noncomputable def nb087AlphaDummy013 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cv (nb087AlphaDummy004 C d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_014`. -/
@[expose]
noncomputable def nb087AlphaDummy014 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cv (nb087AlphaDummy004 C d))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_015`. -/
@[expose]
noncomputable def nb087AlphaDummy015 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb087AlphaDummy011 A B C R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb087AlphaDummy011 A B C R)) (synC1c))).fv ∪
      ((Class.cv (nb087AlphaDummy011 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_016`. -/
@[expose]
noncomputable def nb087AlphaDummy016 (C : Class) (d : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb087AlphaDummy013 C d)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb087AlphaDummy013 C d)) (synC1c))).fv ∪
      ((Class.cv (nb087AlphaDummy013 C d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_017`. -/
@[expose]
noncomputable def nb087AlphaDummy017 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_018`. -/
@[expose]
noncomputable def nb087AlphaDummy018 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_019`. -/
@[expose]
noncomputable def nb087AlphaDummy019 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_020`. -/
@[expose]
noncomputable def nb087AlphaDummy020 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_021`. -/
@[expose]
noncomputable def nb087AlphaDummy021 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_022`. -/
@[expose]
noncomputable def nb087AlphaDummy022 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_023`. -/
@[expose]
noncomputable def nb087AlphaDummy023 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
          (Class.cv (nb087AlphaDummy019 A B C R)))).fv ∪
      ((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
          (Class.cv (nb087AlphaDummy019 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_024`. -/
@[expose]
noncomputable def nb087AlphaDummy024 (C : Class) (d : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb087AlphaDummy021 C d))
          (Class.cv (nb087AlphaDummy022 C d)))).fv ∪
      ((synCnin (Class.cv (nb087AlphaDummy021 C d))
          (Class.cv (nb087AlphaDummy022 C d)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_025`. -/
@[expose]
noncomputable def nb087AlphaDummy025 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
      ((Class.cv (nb087AlphaDummy019 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_026`. -/
@[expose]
noncomputable def nb087AlphaDummy026 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
      ((Class.cv (nb087AlphaDummy022 C d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_027`. -/
@[expose]
noncomputable def nb087AlphaDummy027 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb087AlphaDummy018 A B C R)))).fv ∪
      ((synCcompl (Class.cv (nb087AlphaDummy019 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_028`. -/
@[expose]
noncomputable def nb087AlphaDummy028 (C : Class) (d : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb087AlphaDummy021 C d)))).fv ∪
      ((synCcompl (Class.cv (nb087AlphaDummy022 C d)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_029`. -/
@[expose]
noncomputable def nb087AlphaDummy029 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
      ((Class.cv (nb087AlphaDummy018 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_030`. -/
@[expose]
noncomputable def nb087AlphaDummy030 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
      ((Class.cv (nb087AlphaDummy021 C d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_031`. -/
@[expose]
noncomputable def nb087AlphaDummy031 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb087AlphaDummy019 A B C R))).fv ∪
      ((Class.cv (nb087AlphaDummy019 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_032`. -/
@[expose]
noncomputable def nb087AlphaDummy032 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cv (nb087AlphaDummy022 C d))).fv ∪
      ((Class.cv (nb087AlphaDummy022 C d))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_033`. -/
@[expose]
noncomputable def nb087AlphaDummy033 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb087AlphaDummy001 A B C R)
          (synWrex (nb087AlphaDummy002 A B C R) C
            (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
              (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb087AlphaDummy001 A B C R)
          (synWrex (nb087AlphaDummy002 A B C R) C
            (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
              (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_034`. -/
@[expose]
noncomputable def nb087AlphaDummy034 (C : Class) (d : Var) : Var :=
  (freshVar (((Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
            (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
              (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb087AlphaDummy003 C d)
          (synWrex (nb087AlphaDummy004 C d) C
            (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
              (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_035`. -/
@[expose]
noncomputable def nb087AlphaDummy035 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_036`. -/
@[expose]
noncomputable def nb087AlphaDummy036 (C : Class) (d : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb087AlphaDummy004 C d))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_037`. -/
@[expose]
noncomputable def nb087AlphaDummy037 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb087AlphaDummy002 A B C R)))).fv ∪
      ((synCphi (Class.cv (nb087AlphaDummy002 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb087_alpha_dummy_038`. -/
@[expose]
noncomputable def nb087AlphaDummy038 (C : Class) (d : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb087AlphaDummy004 C d)))).fv ∪
      ((synCphi (Class.cv (nb087AlphaDummy004 C d)))).fv) 0)

theorem nb087_fresh_000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy007 A B C R) ∉
      (((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R)
              (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))))).fv ∪
        ((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R)
              (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))))).fv) :=
  by
  simpa only [nb087AlphaDummy007] using
    freshVar_not_mem
      (((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R)
              (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))))).fv ∪
        ((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R)
              (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))))).fv)
      0

theorem nb087_fresh_001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy033 A B C R) ∉
      (((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R) C
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb087AlphaDummy001 A B C R)
            (synWrex (nb087AlphaDummy002 A B C R) C
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb087AlphaDummy033] using
    freshVar_not_mem
      (((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R) C
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb087AlphaDummy001 A B C R)
            (synWrex (nb087AlphaDummy002 A B C R) C
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb087_fresh_002 (C : Class) (d : Var) :
    (nb087AlphaDummy008 C d) ∉
      (((Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCphi (Class.cv (nb087AlphaDummy004 C d))))))).fv ∪
        ((Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCphi (Class.cv (nb087AlphaDummy004 C d))))))).fv) :=
  by
  simpa only [nb087AlphaDummy008] using
    freshVar_not_mem
      (((Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCphi (Class.cv (nb087AlphaDummy004 C d))))))).fv ∪
        ((Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCphi (Class.cv (nb087AlphaDummy004 C d))))))).fv)
      0

theorem nb087_fresh_003 (C : Class) (d : Var) :
    (nb087AlphaDummy034 C d) ∉
      (((Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) C
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb087AlphaDummy034] using
    freshVar_not_mem
      (((Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) C
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb087_fresh_004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy009 A B C R) ∉ (((Class.cv (nb087AlphaDummy000 A B C R))).fv) :=
  by
  simpa only [nb087AlphaDummy009] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy000 A B C R))).fv) 0

theorem nb087_fresh_005 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy011 A B C R) ∉ (((Class.cv (nb087AlphaDummy002 A B C R))).fv) :=
  by
  simpa only [nb087AlphaDummy011] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy002 A B C R))).fv) 0

theorem nb087_fresh_006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy012 A B C R) ∉ (((Class.cv (nb087AlphaDummy002 A B C R))).fv) :=
  by
  simpa only [nb087AlphaDummy012] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy002 A B C R))).fv) 1

theorem nb087_distinct_007 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy011 A B C R) ≠ (nb087AlphaDummy012 A B C R) := by
  simpa only [nb087AlphaDummy011, nb087AlphaDummy012] using
    (freshVar_injective (((Class.cv (nb087AlphaDummy002 A B C R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb087_fresh_008 (C : Class) (d : Var) :
    (nb087AlphaDummy013 C d) ∉ (((Class.cv (nb087AlphaDummy004 C d))).fv) := by
  simpa only [nb087AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy004 C d))).fv) 0

theorem nb087_fresh_009 (C : Class) (d : Var) :
    (nb087AlphaDummy014 C d) ∉ (((Class.cv (nb087AlphaDummy004 C d))).fv) := by
  simpa only [nb087AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy004 C d))).fv) 1

theorem nb087_distinct_010 (C : Class) (d : Var) :
    (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy014 C d) := by
  simpa only [nb087AlphaDummy013, nb087AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb087AlphaDummy004 C d))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb087_fresh_011 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy017 A B C R) ∉
      (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb087AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) 0

theorem nb087_fresh_012 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy018 A B C R) ∉
      (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb087AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) 1

theorem nb087_fresh_013 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy019 A B C R) ∉
      (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb087AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) 2

theorem nb087_distinct_014 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy017 A B C R) ≠ (nb087AlphaDummy018 A B C R) := by
  simpa only [nb087AlphaDummy017, nb087AlphaDummy018] using
    (freshVar_injective (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb087_distinct_015 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy017 A B C R) ≠ (nb087AlphaDummy019 A B C R) := by
  simpa only [nb087AlphaDummy017, nb087AlphaDummy019] using
    (freshVar_injective (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb087_distinct_016 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy019 A B C R) := by
  simpa only [nb087AlphaDummy018, nb087AlphaDummy019] using
    (freshVar_injective (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb087_fresh_017 (C : Class) (d : Var) :
    (nb087AlphaDummy020 C d) ∉
      (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb087AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) 0

theorem nb087_fresh_018 (C : Class) (d : Var) :
    (nb087AlphaDummy021 C d) ∉
      (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb087AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) 1

theorem nb087_fresh_019 (C : Class) (d : Var) :
    (nb087AlphaDummy022 C d) ∉
      (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb087AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) 2

theorem nb087_distinct_020 (C : Class) (d : Var) :
    (nb087AlphaDummy020 C d) ≠ (nb087AlphaDummy021 C d) := by
  simpa only [nb087AlphaDummy020, nb087AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb087_distinct_021 (C : Class) (d : Var) :
    (nb087AlphaDummy020 C d) ≠ (nb087AlphaDummy022 C d) := by
  simpa only [nb087AlphaDummy020, nb087AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb087_distinct_022 (C : Class) (d : Var) :
    (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy022 C d) := by
  simpa only [nb087AlphaDummy021, nb087AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb087_fresh_023 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy029 A B C R) ∉
      (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy018 A B C R))).fv) :=
  by
  simpa only [nb087AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy018 A B C R))).fv)
      0

theorem nb087_fresh_024 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy025 A B C R) ∉
      (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy019 A B C R))).fv) :=
  by
  simpa only [nb087AlphaDummy025] using
    freshVar_not_mem
      (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy019 A B C R))).fv)
      0

theorem nb087_fresh_025 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy031 A B C R) ∉
      (((Class.cv (nb087AlphaDummy019 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy019 A B C R))).fv) :=
  by
  simpa only [nb087AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb087AlphaDummy019 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy019 A B C R))).fv)
      0

theorem nb087_fresh_026 (C : Class) (d : Var) :
    (nb087AlphaDummy030 C d) ∉
      (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy021 C d))).fv) :=
  by
  simpa only [nb087AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy021 C d))).fv)
      0

theorem nb087_fresh_027 (C : Class) (d : Var) :
    (nb087AlphaDummy026 C d) ∉
      (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy022 C d))).fv) :=
  by
  simpa only [nb087AlphaDummy026] using
    freshVar_not_mem
      (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy022 C d))).fv)
      0

theorem nb087_fresh_028 (C : Class) (d : Var) :
    (nb087AlphaDummy032 C d) ∉
      (((Class.cv (nb087AlphaDummy022 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy022 C d))).fv) :=
  by
  simpa only [nb087AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb087AlphaDummy022 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy022 C d))).fv)
      0

theorem nb087_fresh_029 (d : Var) : (nb087AlphaDummy010 d) ∉ (((Class.cv d)).fv) := by
  simpa only [nb087AlphaDummy010] using freshVar_not_mem (((Class.cv d)).fv) 0

theorem nb087_fresh_030 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy015 A B C R) ∉
      (((Wff.classMem (Class.cv (nb087AlphaDummy011 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb087AlphaDummy011 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb087AlphaDummy011 A B C R))).fv) :=
  by
  simpa only [nb087AlphaDummy015] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb087AlphaDummy011 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb087AlphaDummy011 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb087AlphaDummy011 A B C R))).fv)
      0

theorem nb087_fresh_031 (C : Class) (d : Var) :
    (nb087AlphaDummy016 C d) ∉
      (((Wff.classMem (Class.cv (nb087AlphaDummy013 C d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb087AlphaDummy013 C d)) (synC1c))).fv ∪
        ((Class.cv (nb087AlphaDummy013 C d))).fv) :=
  by
  simpa only [nb087AlphaDummy016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb087AlphaDummy013 C d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb087AlphaDummy013 C d)) (synC1c))).fv ∪
        ((Class.cv (nb087AlphaDummy013 C d))).fv)
      0

theorem nb087_fresh_032 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy005 A B C R) ∉
      (((synCcompl (Class.cab (nb087AlphaDummy001 A B C R)
              (synWrex (nb087AlphaDummy002 A B C R)
                (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb087AlphaDummy001 A B C R)
              (synWrex (nb087AlphaDummy002 A B C R) C
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb087AlphaDummy005] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb087AlphaDummy001 A B C R)
              (synWrex (nb087AlphaDummy002 A B C R)
                (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb087AlphaDummy001 A B C R)
              (synWrex (nb087AlphaDummy002 A B C R) C
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb087_fresh_033 (C : Class) (d : Var) :
    (nb087AlphaDummy006 C d) ∉
      (((synCcompl (Class.cab (nb087AlphaDummy003 C d)
              (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCphi (Class.cv (nb087AlphaDummy004 C d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb087AlphaDummy006] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb087AlphaDummy003 C d)
              (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCphi (Class.cv (nb087AlphaDummy004 C d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb087_fresh_034 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy027 A B C R) ∉
      (((synCcompl (Class.cv (nb087AlphaDummy018 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb087AlphaDummy019 A B C R)))).fv) :=
  by
  simpa only [nb087AlphaDummy027] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb087AlphaDummy018 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb087AlphaDummy019 A B C R)))).fv)
      0

theorem nb087_fresh_035 (C : Class) (d : Var) :
    (nb087AlphaDummy028 C d) ∉
      (((synCcompl (Class.cv (nb087AlphaDummy021 C d)))).fv ∪
        ((synCcompl (Class.cv (nb087AlphaDummy022 C d)))).fv) :=
  by
  simpa only [nb087AlphaDummy028] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb087AlphaDummy021 C d)))).fv ∪
        ((synCcompl (Class.cv (nb087AlphaDummy022 C d)))).fv)
      0

theorem nb087_fresh_036 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy035 A B C R) ∉
      (((synCcompl (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb087AlphaDummy035] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb087_fresh_037 (C : Class) (d : Var) :
    (nb087AlphaDummy036 C d) ∉
      (((synCcompl (synCphi (Class.cv (nb087AlphaDummy004 C d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb087AlphaDummy036] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb087AlphaDummy004 C d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb087_fresh_038 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy023 A B C R) ∉
      (((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
            (Class.cv (nb087AlphaDummy019 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
            (Class.cv (nb087AlphaDummy019 A B C R)))).fv) :=
  by
  simpa only [nb087AlphaDummy023] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
            (Class.cv (nb087AlphaDummy019 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
            (Class.cv (nb087AlphaDummy019 A B C R)))).fv)
      0

theorem nb087_fresh_039 (C : Class) (d : Var) :
    (nb087AlphaDummy024 C d) ∉
      (((synCnin (Class.cv (nb087AlphaDummy021 C d))
            (Class.cv (nb087AlphaDummy022 C d)))).fv ∪
        ((synCnin (Class.cv (nb087AlphaDummy021 C d))
            (Class.cv (nb087AlphaDummy022 C d)))).fv) :=
  by
  simpa only [nb087AlphaDummy024] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb087AlphaDummy021 C d))
            (Class.cv (nb087AlphaDummy022 C d)))).fv ∪
        ((synCnin (Class.cv (nb087AlphaDummy021 C d))
            (Class.cv (nb087AlphaDummy022 C d)))).fv)
      0

theorem nb087_fresh_040 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy037 A B C R) ∉
      (((synCphi (Class.cv (nb087AlphaDummy002 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb087AlphaDummy002 A B C R)))).fv) :=
  by
  simpa only [nb087AlphaDummy037] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb087AlphaDummy002 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb087AlphaDummy002 A B C R)))).fv)
      0

theorem nb087_fresh_041 (C : Class) (d : Var) :
    (nb087AlphaDummy038 C d) ∉
      (((synCphi (Class.cv (nb087AlphaDummy004 C d)))).fv ∪
        ((synCphi (Class.cv (nb087AlphaDummy004 C d)))).fv) :=
  by
  simpa only [nb087AlphaDummy038] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb087AlphaDummy004 C d)))).fv ∪
        ((synCphi (Class.cv (nb087AlphaDummy004 C d)))).fv)
      0

theorem nb087_fresh_042 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy001 A B C R) ∉
      (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) :=
  by
  simpa only [nb087AlphaDummy001] using
    freshVar_not_mem (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv)
      0

theorem nb087_fresh_043 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy002 A B C R) ∉
      (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) :=
  by
  simpa only [nb087AlphaDummy002] using
    freshVar_not_mem (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv)
      1

theorem nb087_distinct_044 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy001 A B C R) ≠ (nb087AlphaDummy002 A B C R) := by
  simpa only [nb087AlphaDummy001, nb087AlphaDummy002] using
    (freshVar_injective
      (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) (i := 0) (j :=
      1) (by decide))

theorem nb087_fresh_045 (C : Class) (d : Var) :
    (nb087AlphaDummy003 C d) ∉ (((synCsn (Class.cv d))).fv ∪ (C).fv) := by
  simpa only [nb087AlphaDummy003] using
    freshVar_not_mem (((synCsn (Class.cv d))).fv ∪ (C).fv) 0

theorem nb087_fresh_046 (C : Class) (d : Var) :
    (nb087AlphaDummy004 C d) ∉ (((synCsn (Class.cv d))).fv ∪ (C).fv) := by
  simpa only [nb087AlphaDummy004] using
    freshVar_not_mem (((synCsn (Class.cv d))).fv ∪ (C).fv) 1

theorem nb087_distinct_047 (C : Class) (d : Var) :
    (nb087AlphaDummy003 C d) ≠ (nb087AlphaDummy004 C d) := by
  simpa only [nb087AlphaDummy003, nb087AlphaDummy004] using
    (freshVar_injective (((synCsn (Class.cv d))).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb087_fresh_048 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb087AlphaDummy000] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb087_support_mem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∈
      (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∈
      (((synCcompl (Class.cab (nb087AlphaDummy001 A B C R)
              (synWrex (nb087AlphaDummy002 A B C R)
                (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb087AlphaDummy001 A B C R)
              (synWrex (nb087AlphaDummy002 A B C R) C
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy001 A B C R) from (by
          unfold nb087AlphaDummy001;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0000 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy002 A B C R) from (by
            unfold nb087AlphaDummy002;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0000 A B C R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb087_support_mem_0002 (C : Class) (d : Var) :
    d ∈ (((synCsn (Class.cv d))).fv ∪ (C).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0003 (C : Class) (d : Var) :
    d ∈
      (((synCcompl (Class.cab (nb087AlphaDummy003 C d)
              (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCphi (Class.cv (nb087AlphaDummy004 C d)))))))).fv ∪ ((synCcompl
            (Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb087AlphaDummy003 C d) from (by
          unfold nb087AlphaDummy003;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0002 C d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb087AlphaDummy004 C d) from (by
            unfold nb087AlphaDummy004;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0002 C d) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb087_support_mem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∈
      (((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R)
              (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))))).fv ∪
        ((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R)
              (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy001 A B C R) from (by
          unfold nb087AlphaDummy001;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0000 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy002 A B C R) from (by
            unfold nb087AlphaDummy002;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0000 A B C R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb087_support_mem_0005 (C : Class) (d : Var) :
    d ∈
      (((Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCphi (Class.cv (nb087AlphaDummy004 C d))))))).fv ∪
        ((Class.cab (nb087AlphaDummy003 C d)
            (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCphi (Class.cv (nb087AlphaDummy004 C d))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb087AlphaDummy003 C d) from (by
          unfold nb087AlphaDummy003;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0002 C d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb087AlphaDummy004 C d) from (by
            unfold nb087AlphaDummy004;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0002 C d) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb087_support_mem_0006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∈ (((Class.cv (nb087AlphaDummy000 A B C R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0007 (d : Var) : d ∈ (((Class.cv d)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0008 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy002 A B C R) ∈ (((Class.cv (nb087AlphaDummy002 A B C R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0009 (C : Class) (d : Var) :
    (nb087AlphaDummy004 C d) ∈ (((Class.cv (nb087AlphaDummy004 C d))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0010 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy011 A B C R) ∈
      (((Wff.classMem (Class.cv (nb087AlphaDummy011 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb087AlphaDummy011 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb087AlphaDummy011 A B C R))).fv) :=
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

theorem nb087_support_mem_0011 (C : Class) (d : Var) :
    (nb087AlphaDummy013 C d) ∈
      (((Wff.classMem (Class.cv (nb087AlphaDummy013 C d)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb087AlphaDummy013 C d)) (synC1c))).fv ∪
        ((Class.cv (nb087AlphaDummy013 C d))).fv) :=
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

theorem nb087_support_mem_0012 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy011 A B C R) ∈
      (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0013 (C : Class) (d : Var) :
    (nb087AlphaDummy013 C d) ∈
      (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0014 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy018 A B C R) ∈
      (((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
            (Class.cv (nb087AlphaDummy019 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
            (Class.cv (nb087AlphaDummy019 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0015 (C : Class) (d : Var) :
    (nb087AlphaDummy021 C d) ∈
      (((synCnin (Class.cv (nb087AlphaDummy021 C d))
            (Class.cv (nb087AlphaDummy022 C d)))).fv ∪
        ((synCnin (Class.cv (nb087AlphaDummy021 C d))
            (Class.cv (nb087AlphaDummy022 C d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0016 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy018 A B C R) ∈
      (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy019 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0017 (C : Class) (d : Var) :
    (nb087AlphaDummy021 C d) ∈
      (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy022 C d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0018 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy019 A B C R) ∈
      (((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
            (Class.cv (nb087AlphaDummy019 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb087AlphaDummy018 A B C R))
            (Class.cv (nb087AlphaDummy019 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0019 (C : Class) (d : Var) :
    (nb087AlphaDummy022 C d) ∈
      (((synCnin (Class.cv (nb087AlphaDummy021 C d))
            (Class.cv (nb087AlphaDummy022 C d)))).fv ∪
        ((synCnin (Class.cv (nb087AlphaDummy021 C d))
            (Class.cv (nb087AlphaDummy022 C d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0020 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy019 A B C R) ∈
      (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy019 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0021 (C : Class) (d : Var) :
    (nb087AlphaDummy022 C d) ∈
      (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy022 C d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0022 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy018 A B C R) ∈
      (((synCcompl (Class.cv (nb087AlphaDummy018 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb087AlphaDummy019 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0023 (C : Class) (d : Var) :
    (nb087AlphaDummy021 C d) ∈
      (((synCcompl (Class.cv (nb087AlphaDummy021 C d)))).fv ∪
        ((synCcompl (Class.cv (nb087AlphaDummy022 C d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0024 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy018 A B C R) ∈
      (((Class.cv (nb087AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy018 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0025 (C : Class) (d : Var) :
    (nb087AlphaDummy021 C d) ∈
      (((Class.cv (nb087AlphaDummy021 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy021 C d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0026 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy019 A B C R) ∈
      (((synCcompl (Class.cv (nb087AlphaDummy018 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb087AlphaDummy019 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0027 (C : Class) (d : Var) :
    (nb087AlphaDummy022 C d) ∈
      (((synCcompl (Class.cv (nb087AlphaDummy021 C d)))).fv ∪
        ((synCcompl (Class.cv (nb087AlphaDummy022 C d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0028 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy019 A B C R) ∈
      (((Class.cv (nb087AlphaDummy019 A B C R))).fv ∪
        ((Class.cv (nb087AlphaDummy019 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0029 (C : Class) (d : Var) :
    (nb087AlphaDummy022 C d) ∈
      (((Class.cv (nb087AlphaDummy022 C d))).fv ∪
        ((Class.cv (nb087AlphaDummy022 C d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0030 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy002 A B C R) ∈
      (((synCcompl (synCphi (Class.cv (nb087AlphaDummy002 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0031 (C : Class) (d : Var) :
    (nb087AlphaDummy004 C d) ∈
      (((synCcompl (synCphi (Class.cv (nb087AlphaDummy004 C d))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0032 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy002 A B C R) ∈
      (((synCphi (Class.cv (nb087AlphaDummy002 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb087AlphaDummy002 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0033 (C : Class) (d : Var) :
    (nb087AlphaDummy004 C d) ∈
      (((synCphi (Class.cv (nb087AlphaDummy004 C d)))).fv ∪
        ((synCphi (Class.cv (nb087AlphaDummy004 C d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C087C001Part002`. -/


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

theorem nb087_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy002 A B C R) ∉ C.fv :=
  by
  change
    freshVar (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) 1 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_focused_notmem_0001 (C : Class) (d : Var) :
    (nb087AlphaDummy004 C d) ∉ C.fv :=
  by
  change freshVar (((synCsn (Class.cv d))).fv ∪ (C).fv) 1 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy001 A B C R) ∉ C.fv :=
  by
  change
    freshVar (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_focused_notmem_0003 (C : Class) (d : Var) :
    (nb087AlphaDummy003 C d) ∉ C.fv :=
  by
  change freshVar (((synCsn (Class.cv d))).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_focused_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy033 A B C R) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R) C
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                    (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb087AlphaDummy001 A B C R)
              (synWrex (nb087AlphaDummy002 A B C R) C
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                    (synCsn (synC0c))))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb087AlphaDummy001 A B C R)
      (synWrex (nb087AlphaDummy002 A B C R) C
        (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
          (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R))) (synCsn (synC0c)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb087_focused_notmem_0002 A B C R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb087AlphaDummy002 A B C R) C
        (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
          (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R))) (synCsn (synC0c))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb087_focused_notmem_0000 A B C R)) (h_eq ▸ hu)
    · exact hu

theorem nb087_focused_notmem_0005 (C : Class) (d : Var) :
    (nb087AlphaDummy034 C d) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                    (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb087AlphaDummy003 C d)
              (synWrex (nb087AlphaDummy004 C d) C
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                    (synCsn (synC0c))))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb087AlphaDummy003 C d)
      (synWrex (nb087AlphaDummy004 C d) C
        (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
          (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d))) (synCsn (synC0c)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb087_focused_notmem_0003 C d)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb087AlphaDummy004 C d) C
        (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
          (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d))) (synCsn (synC0c))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb087_focused_notmem_0001 C d)) (h_eq ▸ hu)
    · exact hu

theorem nb087_focused_notmem_0006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy005 A B C R) ∉ C.fv :=
  by
  change
    freshVar
        (((synCcompl (Class.cab (nb087AlphaDummy001 A B C R)
                (synWrex (nb087AlphaDummy002 A B C R)
                  (synCsn (Class.cv (nb087AlphaDummy000 A B C R)))
                  (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                    (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))))))).fv ∪ ((synCcompl
              (Class.cab (nb087AlphaDummy001 A B C R)
                (synWrex (nb087AlphaDummy002 A B C R) C
                  (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                    (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                      (synCsn (synC0c)))))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl
      (Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R) C
          (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
            (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
              (synCsn (synC0c))))))]
  rw [fv_class_cab (nb087AlphaDummy001 A B C R)
      (synWrex (nb087AlphaDummy002 A B C R) C
        (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
          (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R))) (synCsn (synC0c)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb087_focused_notmem_0002 A B C R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb087AlphaDummy002 A B C R) C
        (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
          (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R))) (synCsn (synC0c))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb087_focused_notmem_0000 A B C R)) (h_eq ▸ hu)
    · exact hu

theorem nb087_focused_notmem_0007 (C : Class) (d : Var) :
    (nb087AlphaDummy006 C d) ∉ C.fv :=
  by
  change
    freshVar
        (((synCcompl (Class.cab (nb087AlphaDummy003 C d)
                (synWrex (nb087AlphaDummy004 C d) (synCsn (Class.cv d))
                  (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                    (synCphi (Class.cv (nb087AlphaDummy004 C d)))))))).fv ∪ ((synCcompl
              (Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
                  (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                    (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                      (synCsn (synC0c)))))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl
      (Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
          (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
            (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d))) (synCsn (synC0c))))))]
  rw [fv_class_cab (nb087AlphaDummy003 C d)
      (synWrex (nb087AlphaDummy004 C d) C
        (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
          (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d))) (synCsn (synC0c)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb087_focused_notmem_0003 C d)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb087AlphaDummy004 C d) C
        (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
          (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d))) (synCsn (synC0c))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb087_focused_notmem_0001 C d)) (h_eq ▸ hu)
    · exact hu

theorem nb087_focused_notmem_0008 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_compact_envfresh_0003 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_C_d : d ∉ C.fv) :
    TEnvFresh
      [((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)]
      C.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb087AlphaDummy002 A B C R) (nb087AlphaDummy004 C d)
      (nb087_focused_notmem_0000 A B C R) (nb087_focused_notmem_0001 C d)
      (TEnvFresh.consFresh (nb087AlphaDummy001 A B C R) (nb087AlphaDummy003 C d)
        (nb087_focused_notmem_0002 A B C R) (nb087_focused_notmem_0003 C d)
        (TEnvFresh.consFresh (nb087AlphaDummy033 A B C R) (nb087AlphaDummy034 C d)
          (nb087_focused_notmem_0004 A B C R) (nb087_focused_notmem_0005 C d)
          (TEnvFresh.consFresh (nb087AlphaDummy005 A B C R) (nb087AlphaDummy006 C d)
            (nb087_focused_notmem_0006 A B C R) (nb087_focused_notmem_0007 C d)
            (TEnvFresh.consFresh (nb087AlphaDummy000 A B C R) d
              (nb087_focused_notmem_0008 A B C R) dv_C_d (TEnvFresh.nil C.fv))))))

/-- Checked nominal proof certificate identified upstream as `nb087_focused_refl_0000`. -/
@[expose]
noncomputable def nb087FocusedRefl0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_C_d : d ∉ C.fv) :
    TReflOn
      [((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)]
      C.fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0003 A B C R d dv_C_d)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
