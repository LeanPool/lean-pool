/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C083C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_000`. -/
@[expose]
noncomputable def nb083AlphaDummy000 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_001`. -/
@[expose]
noncomputable def nb083AlphaDummy001 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_002`. -/
@[expose]
noncomputable def nb083AlphaDummy002 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
      ((Class.cv (nb083AlphaDummy001 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_003`. -/
@[expose]
noncomputable def nb083AlphaDummy003 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
      ((Class.cv (nb083AlphaDummy001 A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_004`. -/
@[expose]
noncomputable def nb083AlphaDummy004 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv b)).fv ∪ ((Class.cv c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_005`. -/
@[expose]
noncomputable def nb083AlphaDummy005 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv b)).fv ∪ ((Class.cv c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_006`. -/
@[expose]
noncomputable def nb083AlphaDummy006 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb083AlphaDummy002 A B C R)
            (synWrex (nb083AlphaDummy003 A B C R) (Class.cv (nb083AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_007`. -/
@[expose]
noncomputable def nb083AlphaDummy007 (b : Var) (c : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCphi (Class.cv (nb083AlphaDummy005 b c)))))))).fv ∪ ((synCcompl
          (Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_008`. -/
@[expose]
noncomputable def nb083AlphaDummy008 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb083AlphaDummy002 A B C R)
          (synWrex (nb083AlphaDummy003 A B C R) (Class.cv (nb083AlphaDummy000 A B C R))
            (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
              (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))))).fv ∪
      ((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
            (Class.cv (nb083AlphaDummy000 A B C R))
            (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
              (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_009`. -/
@[expose]
noncomputable def nb083AlphaDummy009 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cab (nb083AlphaDummy004 b c)
          (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
            (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
              (synCphi (Class.cv (nb083AlphaDummy005 b c))))))).fv ∪
      ((Class.cab (nb083AlphaDummy004 b c) (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
            (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
              (synCphi (Class.cv (nb083AlphaDummy005 b c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_010`. -/
@[expose]
noncomputable def nb083AlphaDummy010 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy003 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_011`. -/
@[expose]
noncomputable def nb083AlphaDummy011 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy003 A B C R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_012`. -/
@[expose]
noncomputable def nb083AlphaDummy012 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083AlphaDummy005 b c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_013`. -/
@[expose]
noncomputable def nb083AlphaDummy013 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083AlphaDummy005 b c))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_014`. -/
@[expose]
noncomputable def nb083AlphaDummy014 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb083AlphaDummy010 A B C R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb083AlphaDummy010 A B C R)) (synC1c))).fv ∪
      ((Class.cv (nb083AlphaDummy010 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_015`. -/
@[expose]
noncomputable def nb083AlphaDummy015 (b : Var) (c : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb083AlphaDummy012 b c)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb083AlphaDummy012 b c)) (synC1c))).fv ∪
      ((Class.cv (nb083AlphaDummy012 b c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_016`. -/
@[expose]
noncomputable def nb083AlphaDummy016 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_017`. -/
@[expose]
noncomputable def nb083AlphaDummy017 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_018`. -/
@[expose]
noncomputable def nb083AlphaDummy018 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_019`. -/
@[expose]
noncomputable def nb083AlphaDummy019 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_020`. -/
@[expose]
noncomputable def nb083AlphaDummy020 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_021`. -/
@[expose]
noncomputable def nb083AlphaDummy021 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_022`. -/
@[expose]
noncomputable def nb083AlphaDummy022 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
          (Class.cv (nb083AlphaDummy018 A B C R)))).fv ∪
      ((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
          (Class.cv (nb083AlphaDummy018 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_023`. -/
@[expose]
noncomputable def nb083AlphaDummy023 (b : Var) (c : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb083AlphaDummy020 b c))
          (Class.cv (nb083AlphaDummy021 b c)))).fv ∪
      ((synCnin (Class.cv (nb083AlphaDummy020 b c))
          (Class.cv (nb083AlphaDummy021 b c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_024`. -/
@[expose]
noncomputable def nb083AlphaDummy024 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
      ((Class.cv (nb083AlphaDummy018 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_025`. -/
@[expose]
noncomputable def nb083AlphaDummy025 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
      ((Class.cv (nb083AlphaDummy021 b c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_026`. -/
@[expose]
noncomputable def nb083AlphaDummy026 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb083AlphaDummy017 A B C R)))).fv ∪
      ((synCcompl (Class.cv (nb083AlphaDummy018 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_027`. -/
@[expose]
noncomputable def nb083AlphaDummy027 (b : Var) (c : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb083AlphaDummy020 b c)))).fv ∪
      ((synCcompl (Class.cv (nb083AlphaDummy021 b c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_028`. -/
@[expose]
noncomputable def nb083AlphaDummy028 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
      ((Class.cv (nb083AlphaDummy017 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_029`. -/
@[expose]
noncomputable def nb083AlphaDummy029 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
      ((Class.cv (nb083AlphaDummy020 b c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_030`. -/
@[expose]
noncomputable def nb083AlphaDummy030 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb083AlphaDummy018 A B C R))).fv ∪
      ((Class.cv (nb083AlphaDummy018 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_031`. -/
@[expose]
noncomputable def nb083AlphaDummy031 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cv (nb083AlphaDummy021 b c))).fv ∪
      ((Class.cv (nb083AlphaDummy021 b c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_032`. -/
@[expose]
noncomputable def nb083AlphaDummy032 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb083AlphaDummy002 A B C R)
          (synWrex (nb083AlphaDummy003 A B C R) (Class.cv (nb083AlphaDummy001 A B C R))
            (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
              (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb083AlphaDummy002 A B C R)
          (synWrex (nb083AlphaDummy003 A B C R) (Class.cv (nb083AlphaDummy001 A B C R))
            (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
              (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_033`. -/
@[expose]
noncomputable def nb083AlphaDummy033 (b : Var) (c : Var) : Var :=
  (freshVar (((Class.cab (nb083AlphaDummy004 b c)
          (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
            (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
              (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb083AlphaDummy004 b c)
          (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
            (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
              (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_034`. -/
@[expose]
noncomputable def nb083AlphaDummy034 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_035`. -/
@[expose]
noncomputable def nb083AlphaDummy035 (b : Var) (c : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb083AlphaDummy005 b c))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_036`. -/
@[expose]
noncomputable def nb083AlphaDummy036 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb083AlphaDummy003 A B C R)))).fv ∪
      ((synCphi (Class.cv (nb083AlphaDummy003 A B C R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb083_alpha_dummy_037`. -/
@[expose]
noncomputable def nb083AlphaDummy037 (b : Var) (c : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb083AlphaDummy005 b c)))).fv ∪
      ((synCphi (Class.cv (nb083AlphaDummy005 b c)))).fv) 0)

theorem nb083_fresh_000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy008 A B C R) ∉
      (((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))))).fv ∪
        ((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))))).fv) :=
  by
  simpa only [nb083AlphaDummy008] using
    freshVar_not_mem
      (((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))))).fv ∪
        ((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))))).fv)
      0

theorem nb083_fresh_001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy032 A B C R) ∉
      (((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb083AlphaDummy002 A B C R)
            (synWrex (nb083AlphaDummy003 A B C R) (Class.cv (nb083AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb083AlphaDummy032] using
    freshVar_not_mem
      (((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb083AlphaDummy002 A B C R)
            (synWrex (nb083AlphaDummy003 A B C R) (Class.cv (nb083AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb083_fresh_002 (b : Var) (c : Var) :
    (nb083AlphaDummy009 b c) ∉
      (((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCphi (Class.cv (nb083AlphaDummy005 b c))))))).fv ∪
        ((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCphi (Class.cv (nb083AlphaDummy005 b c))))))).fv) :=
  by
  simpa only [nb083AlphaDummy009] using
    freshVar_not_mem
      (((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCphi (Class.cv (nb083AlphaDummy005 b c))))))).fv ∪
        ((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCphi (Class.cv (nb083AlphaDummy005 b c))))))).fv)
      0

theorem nb083_fresh_003 (b : Var) (c : Var) :
    (nb083AlphaDummy033 b c) ∉
      (((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb083AlphaDummy033] using
    freshVar_not_mem
      (((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb083_fresh_004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy002 A B C R) ∉
      (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv) :=
  by
  simpa only [nb083AlphaDummy002] using
    freshVar_not_mem
      (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv)
      0

theorem nb083_fresh_005 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy003 A B C R) ∉
      (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv) :=
  by
  simpa only [nb083AlphaDummy003] using
    freshVar_not_mem
      (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv)
      1

theorem nb083_distinct_006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy002 A B C R) ≠ (nb083AlphaDummy003 A B C R) := by
  simpa only [nb083AlphaDummy002, nb083AlphaDummy003] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv) (i := 0) (j := 1) (by decide))

theorem nb083_fresh_007 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy010 A B C R) ∉ (((Class.cv (nb083AlphaDummy003 A B C R))).fv) :=
  by
  simpa only [nb083AlphaDummy010] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy003 A B C R))).fv) 0

theorem nb083_fresh_008 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy011 A B C R) ∉ (((Class.cv (nb083AlphaDummy003 A B C R))).fv) :=
  by
  simpa only [nb083AlphaDummy011] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy003 A B C R))).fv) 1

theorem nb083_distinct_009 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy010 A B C R) ≠ (nb083AlphaDummy011 A B C R) := by
  simpa only [nb083AlphaDummy010, nb083AlphaDummy011] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy003 A B C R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb083_fresh_010 (b : Var) (c : Var) :
    (nb083AlphaDummy012 b c) ∉ (((Class.cv (nb083AlphaDummy005 b c))).fv) := by
  simpa only [nb083AlphaDummy012] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy005 b c))).fv) 0

theorem nb083_fresh_011 (b : Var) (c : Var) :
    (nb083AlphaDummy013 b c) ∉ (((Class.cv (nb083AlphaDummy005 b c))).fv) := by
  simpa only [nb083AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy005 b c))).fv) 1

theorem nb083_distinct_012 (b : Var) (c : Var) :
    (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy013 b c) := by
  simpa only [nb083AlphaDummy012, nb083AlphaDummy013] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy005 b c))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb083_fresh_013 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy016 A B C R) ∉
      (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb083AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) 0

theorem nb083_fresh_014 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy017 A B C R) ∉
      (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb083AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) 1

theorem nb083_fresh_015 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy018 A B C R) ∉
      (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb083AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) 2

theorem nb083_distinct_016 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy016 A B C R) ≠ (nb083AlphaDummy017 A B C R) := by
  simpa only [nb083AlphaDummy016, nb083AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb083_distinct_017 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy016 A B C R) ≠ (nb083AlphaDummy018 A B C R) := by
  simpa only [nb083AlphaDummy016, nb083AlphaDummy018] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb083_distinct_018 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy017 A B C R) ≠ (nb083AlphaDummy018 A B C R) := by
  simpa only [nb083AlphaDummy017, nb083AlphaDummy018] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb083_fresh_019 (b : Var) (c : Var) :
    (nb083AlphaDummy019 b c) ∉
      (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb083AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) 0

theorem nb083_fresh_020 (b : Var) (c : Var) :
    (nb083AlphaDummy020 b c) ∉
      (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb083AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) 1

theorem nb083_fresh_021 (b : Var) (c : Var) :
    (nb083AlphaDummy021 b c) ∉
      (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb083AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) 2

theorem nb083_distinct_022 (b : Var) (c : Var) :
    (nb083AlphaDummy019 b c) ≠ (nb083AlphaDummy020 b c) := by
  simpa only [nb083AlphaDummy019, nb083AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb083_distinct_023 (b : Var) (c : Var) :
    (nb083AlphaDummy019 b c) ≠ (nb083AlphaDummy021 b c) := by
  simpa only [nb083AlphaDummy019, nb083AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb083_distinct_024 (b : Var) (c : Var) :
    (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy021 b c) := by
  simpa only [nb083AlphaDummy020, nb083AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb083_fresh_025 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy028 A B C R) ∉
      (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy017 A B C R))).fv) :=
  by
  simpa only [nb083AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy017 A B C R))).fv)
      0

theorem nb083_fresh_026 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy024 A B C R) ∉
      (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy018 A B C R))).fv) :=
  by
  simpa only [nb083AlphaDummy024] using
    freshVar_not_mem
      (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy018 A B C R))).fv)
      0

theorem nb083_fresh_027 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy030 A B C R) ∉
      (((Class.cv (nb083AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy018 A B C R))).fv) :=
  by
  simpa only [nb083AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb083AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy018 A B C R))).fv)
      0

theorem nb083_fresh_028 (b : Var) (c : Var) :
    (nb083AlphaDummy029 b c) ∉
      (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy020 b c))).fv) :=
  by
  simpa only [nb083AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy020 b c))).fv)
      0

theorem nb083_fresh_029 (b : Var) (c : Var) :
    (nb083AlphaDummy025 b c) ∉
      (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy021 b c))).fv) :=
  by
  simpa only [nb083AlphaDummy025] using
    freshVar_not_mem
      (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy021 b c))).fv)
      0

theorem nb083_fresh_030 (b : Var) (c : Var) :
    (nb083AlphaDummy031 b c) ∉
      (((Class.cv (nb083AlphaDummy021 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy021 b c))).fv) :=
  by
  simpa only [nb083AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb083AlphaDummy021 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy021 b c))).fv)
      0

theorem nb083_fresh_031 (b : Var) (c : Var) :
    (nb083AlphaDummy004 b c) ∉ (((Class.cv b)).fv ∪ ((Class.cv c)).fv) := by
  simpa only [nb083AlphaDummy004] using
    freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv c)).fv) 0

theorem nb083_fresh_032 (b : Var) (c : Var) :
    (nb083AlphaDummy005 b c) ∉ (((Class.cv b)).fv ∪ ((Class.cv c)).fv) := by
  simpa only [nb083AlphaDummy005] using
    freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv c)).fv) 1

theorem nb083_distinct_033 (b : Var) (c : Var) :
    (nb083AlphaDummy004 b c) ≠ (nb083AlphaDummy005 b c) := by
  simpa only [nb083AlphaDummy004, nb083AlphaDummy005] using
    (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv c)).fv) (i := 0) (j := 1) (by decide))

theorem nb083_fresh_034 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy014 A B C R) ∉
      (((Wff.classMem (Class.cv (nb083AlphaDummy010 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb083AlphaDummy010 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb083AlphaDummy010 A B C R))).fv) :=
  by
  simpa only [nb083AlphaDummy014] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb083AlphaDummy010 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb083AlphaDummy010 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb083AlphaDummy010 A B C R))).fv)
      0

theorem nb083_fresh_035 (b : Var) (c : Var) :
    (nb083AlphaDummy015 b c) ∉
      (((Wff.classMem (Class.cv (nb083AlphaDummy012 b c)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb083AlphaDummy012 b c)) (synC1c))).fv ∪
        ((Class.cv (nb083AlphaDummy012 b c))).fv) :=
  by
  simpa only [nb083AlphaDummy015] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb083AlphaDummy012 b c)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb083AlphaDummy012 b c)) (synC1c))).fv ∪
        ((Class.cv (nb083AlphaDummy012 b c))).fv)
      0

theorem nb083_fresh_036 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy006 A B C R) ∉
      (((synCcompl (Class.cab (nb083AlphaDummy002 A B C R)
              (synWrex (nb083AlphaDummy003 A B C R)
                (Class.cv (nb083AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                  (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
                (Class.cv (nb083AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                  (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb083AlphaDummy006] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb083AlphaDummy002 A B C R)
              (synWrex (nb083AlphaDummy003 A B C R)
                (Class.cv (nb083AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                  (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
                (Class.cv (nb083AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                  (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb083_fresh_037 (b : Var) (c : Var) :
    (nb083AlphaDummy007 b c) ∉
      (((synCcompl (Class.cab (nb083AlphaDummy004 b c)
              (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
                (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                  (synCphi (Class.cv (nb083AlphaDummy005 b c)))))))).fv ∪ ((synCcompl
            (Class.cab (nb083AlphaDummy004 b c)
              (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                  (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb083AlphaDummy007] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb083AlphaDummy004 b c)
              (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
                (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                  (synCphi (Class.cv (nb083AlphaDummy005 b c)))))))).fv ∪ ((synCcompl
            (Class.cab (nb083AlphaDummy004 b c)
              (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                  (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb083_fresh_038 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy026 A B C R) ∉
      (((synCcompl (Class.cv (nb083AlphaDummy017 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb083AlphaDummy018 A B C R)))).fv) :=
  by
  simpa only [nb083AlphaDummy026] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb083AlphaDummy017 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb083AlphaDummy018 A B C R)))).fv)
      0

theorem nb083_fresh_039 (b : Var) (c : Var) :
    (nb083AlphaDummy027 b c) ∉
      (((synCcompl (Class.cv (nb083AlphaDummy020 b c)))).fv ∪
        ((synCcompl (Class.cv (nb083AlphaDummy021 b c)))).fv) :=
  by
  simpa only [nb083AlphaDummy027] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb083AlphaDummy020 b c)))).fv ∪
        ((synCcompl (Class.cv (nb083AlphaDummy021 b c)))).fv)
      0

theorem nb083_fresh_040 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy034 A B C R) ∉
      (((synCcompl (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb083AlphaDummy034] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb083_fresh_041 (b : Var) (c : Var) :
    (nb083AlphaDummy035 b c) ∉
      (((synCcompl (synCphi (Class.cv (nb083AlphaDummy005 b c))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb083AlphaDummy035] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb083AlphaDummy005 b c))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb083_fresh_042 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy022 A B C R) ∉
      (((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
            (Class.cv (nb083AlphaDummy018 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
            (Class.cv (nb083AlphaDummy018 A B C R)))).fv) :=
  by
  simpa only [nb083AlphaDummy022] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
            (Class.cv (nb083AlphaDummy018 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
            (Class.cv (nb083AlphaDummy018 A B C R)))).fv)
      0

theorem nb083_fresh_043 (b : Var) (c : Var) :
    (nb083AlphaDummy023 b c) ∉
      (((synCnin (Class.cv (nb083AlphaDummy020 b c))
            (Class.cv (nb083AlphaDummy021 b c)))).fv ∪
        ((synCnin (Class.cv (nb083AlphaDummy020 b c))
            (Class.cv (nb083AlphaDummy021 b c)))).fv) :=
  by
  simpa only [nb083AlphaDummy023] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb083AlphaDummy020 b c))
            (Class.cv (nb083AlphaDummy021 b c)))).fv ∪
        ((synCnin (Class.cv (nb083AlphaDummy020 b c))
            (Class.cv (nb083AlphaDummy021 b c)))).fv)
      0

theorem nb083_fresh_044 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy036 A B C R) ∉
      (((synCphi (Class.cv (nb083AlphaDummy003 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb083AlphaDummy003 A B C R)))).fv) :=
  by
  simpa only [nb083AlphaDummy036] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb083AlphaDummy003 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb083AlphaDummy003 A B C R)))).fv)
      0

theorem nb083_fresh_045 (b : Var) (c : Var) :
    (nb083AlphaDummy037 b c) ∉
      (((synCphi (Class.cv (nb083AlphaDummy005 b c)))).fv ∪
        ((synCphi (Class.cv (nb083AlphaDummy005 b c)))).fv) :=
  by
  simpa only [nb083AlphaDummy037] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb083AlphaDummy005 b c)))).fv ∪
        ((synCphi (Class.cv (nb083AlphaDummy005 b c)))).fv)
      0

theorem nb083_fresh_046 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb083AlphaDummy000] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb083_fresh_047 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy001 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb083AlphaDummy001] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1

theorem nb083_distinct_048 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy001 A B C R) := by
  simpa only [nb083AlphaDummy000, nb083AlphaDummy001] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb083_support_mem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ∈
      (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ∈
      (((synCcompl (Class.cab (nb083AlphaDummy002 A B C R)
              (synWrex (nb083AlphaDummy003 A B C R)
                (Class.cv (nb083AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                  (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
                (Class.cv (nb083AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                  (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy002 A B C R) from (by
          unfold nb083AlphaDummy002;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0000 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy003 A B C R) from (by
            unfold nb083AlphaDummy003;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0000 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0002 (b : Var) (c : Var) :
    b ∈ (((Class.cv b)).fv ∪ ((Class.cv c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0003 (b : Var) (c : Var) :
    b ∈
      (((synCcompl (Class.cab (nb083AlphaDummy004 b c)
              (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
                (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                  (synCphi (Class.cv (nb083AlphaDummy005 b c)))))))).fv ∪ ((synCcompl
            (Class.cab (nb083AlphaDummy004 b c)
              (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                  (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb083AlphaDummy004 b c) from (by
          unfold nb083AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0002 b c) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb083AlphaDummy005 b c) from (by
            unfold nb083AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0002 b c) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ∈
      (((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))))).fv ∪
        ((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy000 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy002 A B C R) from (by
          unfold nb083AlphaDummy002;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0000 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy003 A B C R) from (by
            unfold nb083AlphaDummy003;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0000 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0005 (b : Var) (c : Var) :
    b ∈
      (((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCphi (Class.cv (nb083AlphaDummy005 b c))))))).fv ∪
        ((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCphi (Class.cv (nb083AlphaDummy005 b c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb083AlphaDummy004 b c) from (by
          unfold nb083AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0002 b c) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb083AlphaDummy005 b c) from (by
            unfold nb083AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0002 b c) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy003 A B C R) ∈ (((Class.cv (nb083AlphaDummy003 A B C R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0007 (b : Var) (c : Var) :
    (nb083AlphaDummy005 b c) ∈ (((Class.cv (nb083AlphaDummy005 b c))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0008 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy010 A B C R) ∈
      (((Wff.classMem (Class.cv (nb083AlphaDummy010 A B C R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb083AlphaDummy010 A B C R)) (synC1c))).fv ∪
        ((Class.cv (nb083AlphaDummy010 A B C R))).fv) :=
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

theorem nb083_support_mem_0009 (b : Var) (c : Var) :
    (nb083AlphaDummy012 b c) ∈
      (((Wff.classMem (Class.cv (nb083AlphaDummy012 b c)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb083AlphaDummy012 b c)) (synC1c))).fv ∪
        ((Class.cv (nb083AlphaDummy012 b c))).fv) :=
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

theorem nb083_support_mem_0010 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy010 A B C R) ∈
      (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0011 (b : Var) (c : Var) :
    (nb083AlphaDummy012 b c) ∈
      (((Class.cv (nb083AlphaDummy012 b c))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0012 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy017 A B C R) ∈
      (((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
            (Class.cv (nb083AlphaDummy018 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
            (Class.cv (nb083AlphaDummy018 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0013 (b : Var) (c : Var) :
    (nb083AlphaDummy020 b c) ∈
      (((synCnin (Class.cv (nb083AlphaDummy020 b c))
            (Class.cv (nb083AlphaDummy021 b c)))).fv ∪
        ((synCnin (Class.cv (nb083AlphaDummy020 b c))
            (Class.cv (nb083AlphaDummy021 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0014 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy017 A B C R) ∈
      (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy018 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0015 (b : Var) (c : Var) :
    (nb083AlphaDummy020 b c) ∈
      (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy021 b c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0016 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy018 A B C R) ∈
      (((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
            (Class.cv (nb083AlphaDummy018 A B C R)))).fv ∪
        ((synCnin (Class.cv (nb083AlphaDummy017 A B C R))
            (Class.cv (nb083AlphaDummy018 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0017 (b : Var) (c : Var) :
    (nb083AlphaDummy021 b c) ∈
      (((synCnin (Class.cv (nb083AlphaDummy020 b c))
            (Class.cv (nb083AlphaDummy021 b c)))).fv ∪
        ((synCnin (Class.cv (nb083AlphaDummy020 b c))
            (Class.cv (nb083AlphaDummy021 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0018 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy018 A B C R) ∈
      (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy018 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0019 (b : Var) (c : Var) :
    (nb083AlphaDummy021 b c) ∈
      (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy021 b c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0020 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy017 A B C R) ∈
      (((synCcompl (Class.cv (nb083AlphaDummy017 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb083AlphaDummy018 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0021 (b : Var) (c : Var) :
    (nb083AlphaDummy020 b c) ∈
      (((synCcompl (Class.cv (nb083AlphaDummy020 b c)))).fv ∪
        ((synCcompl (Class.cv (nb083AlphaDummy021 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0022 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy017 A B C R) ∈
      (((Class.cv (nb083AlphaDummy017 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy017 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0023 (b : Var) (c : Var) :
    (nb083AlphaDummy020 b c) ∈
      (((Class.cv (nb083AlphaDummy020 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy020 b c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0024 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy018 A B C R) ∈
      (((synCcompl (Class.cv (nb083AlphaDummy017 A B C R)))).fv ∪
        ((synCcompl (Class.cv (nb083AlphaDummy018 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0025 (b : Var) (c : Var) :
    (nb083AlphaDummy021 b c) ∈
      (((synCcompl (Class.cv (nb083AlphaDummy020 b c)))).fv ∪
        ((synCcompl (Class.cv (nb083AlphaDummy021 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0026 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy018 A B C R) ∈
      (((Class.cv (nb083AlphaDummy018 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy018 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0027 (b : Var) (c : Var) :
    (nb083AlphaDummy021 b c) ∈
      (((Class.cv (nb083AlphaDummy021 b c))).fv ∪
        ((Class.cv (nb083AlphaDummy021 b c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0028 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy001 A B C R) ∈
      (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0029 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy001 A B C R) ∈
      (((synCcompl (Class.cab (nb083AlphaDummy002 A B C R)
              (synWrex (nb083AlphaDummy003 A B C R)
                (Class.cv (nb083AlphaDummy000 A B C R))
                (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                  (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
                (Class.cv (nb083AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                  (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb083AlphaDummy001 A B C R) ≠ (nb083AlphaDummy002 A B C R) from (by
          unfold nb083AlphaDummy002;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb083AlphaDummy001 A B C R) ≠ (nb083AlphaDummy003 A B C R) from (by
            unfold nb083AlphaDummy003;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0030 (b : Var) (c : Var) :
    c ∈ (((Class.cv b)).fv ∪ ((Class.cv c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0031 (b : Var) (c : Var) :
    c ∈
      (((synCcompl (Class.cab (nb083AlphaDummy004 b c)
              (synWrex (nb083AlphaDummy005 b c) (Class.cv b)
                (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                  (synCphi (Class.cv (nb083AlphaDummy005 b c)))))))).fv ∪ ((synCcompl
            (Class.cab (nb083AlphaDummy004 b c)
              (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                  (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show c ≠ (nb083AlphaDummy004 b c) from (by
          unfold nb083AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0030 b c) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show c ≠ (nb083AlphaDummy005 b c) from (by
            unfold nb083AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0030 b c) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0032 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy001 A B C R) ∈
      (((Class.cab (nb083AlphaDummy002 A B C R) (synWrex (nb083AlphaDummy003 A B C R)
              (Class.cv (nb083AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb083AlphaDummy002 A B C R)
            (synWrex (nb083AlphaDummy003 A B C R) (Class.cv (nb083AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb083AlphaDummy002 A B C R))
                (synCun (synCphi (Class.cv (nb083AlphaDummy003 A B C R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb083AlphaDummy001 A B C R) ≠ (nb083AlphaDummy002 A B C R) from (by
          unfold nb083AlphaDummy002;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb083AlphaDummy001 A B C R) ≠ (nb083AlphaDummy003 A B C R) from (by
            unfold nb083AlphaDummy003;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0033 (b : Var) (c : Var) :
    c ∈
      (((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb083AlphaDummy004 b c)
            (synWrex (nb083AlphaDummy005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083AlphaDummy004 b c))
                (synCun (synCphi (Class.cv (nb083AlphaDummy005 b c)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show c ≠ (nb083AlphaDummy004 b c) from (by
          unfold nb083AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0030 b c) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show c ≠ (nb083AlphaDummy005 b c) from (by
            unfold nb083AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb083_support_mem_0030 b c) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb083_support_mem_0034 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy003 A B C R) ∈
      (((synCcompl (synCphi (Class.cv (nb083AlphaDummy003 A B C R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0035 (b : Var) (c : Var) :
    (nb083AlphaDummy005 b c) ∈
      (((synCcompl (synCphi (Class.cv (nb083AlphaDummy005 b c))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0036 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy003 A B C R) ∈
      (((synCphi (Class.cv (nb083AlphaDummy003 A B C R)))).fv ∪
        ((synCphi (Class.cv (nb083AlphaDummy003 A B C R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_support_mem_0037 (b : Var) (c : Var) :
    (nb083AlphaDummy005 b c) ∈
      (((synCphi (Class.cv (nb083AlphaDummy005 b c)))).fv ∪
        ((synCphi (Class.cv (nb083AlphaDummy005 b c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb083_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb083_compact_envfresh_0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (dv_A_b : b ∉ A.fv) :
    TEnvFresh [((nb083AlphaDummy000 A B C R), b)] A.fv := by
  exact
    (TEnvFresh.consFresh (nb083AlphaDummy000 A B C R) b
      (nb083_focused_notmem_0000 A B C R) dv_A_b (TEnvFresh.nil A.fv))

/-- Checked nominal proof certificate identified upstream as `nb083_focused_refl_0000`. -/
@[expose]
noncomputable def nb083FocusedRefl0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (dv_A_b : b ∉ A.fv) : TReflOn [((nb083AlphaDummy000 A B C R), b)] A.fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0000 A B C R b dv_A_b)

theorem nb083_focused_notmem_0001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb083_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb083_wpp_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy000 A B C R) ∉ ((synCsep2 B C)).fv := by
  simpa only [nb083AlphaDummy000, fv_syn_csep2, Finset.mem_union, not_or] using
    (And.intro (nb083_focused_notmem_0001 A B C R) (nb083_focused_notmem_0002 A B C R))

theorem nb083_wpp_notmem_0001 (B : Class) (C : Class) (b : Var) (dv_B_b : b ∉ B.fv)
    (dv_C_b : b ∉ C.fv) : b ∉ ((synCsep2 B C)).fv := by
  simpa only [fv_syn_csep2, Finset.mem_union, not_or] using (And.intro dv_B_b dv_C_b)

theorem nb083_compact_envfresh_0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (dv_B_b : b ∉ B.fv) (dv_C_b : b ∉ C.fv) :
    TEnvFresh [((nb083AlphaDummy000 A B C R), b)] ((synCsep2 B C)).fv := by
  exact
    (TEnvFresh.consFresh (nb083AlphaDummy000 A B C R) b (nb083_wpp_notmem_0000 A B C R)
      (nb083_wpp_notmem_0001 B C b dv_B_b dv_C_b) (TEnvFresh.nil ((synCsep2 B C)).fv))

/-- Checked nominal proof certificate identified upstream as `nb083_wpp_refl_0000`. -/
@[expose]
noncomputable def nb083WppRefl0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (dv_B_b : b ∉ B.fv) (dv_C_b : b ∉ C.fv) :
    TReflOn [((nb083AlphaDummy000 A B C R), b)] ((synCsep2 B C)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0001 A B C R b dv_B_b dv_C_b)

theorem nb083_focused_notmem_0003 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy001 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb083_compact_envfresh_0002 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) :
    TEnvFresh [((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb083AlphaDummy001 A B C R) c
      (nb083_focused_notmem_0003 A B C R) dv_A_c
      (TEnvFresh.consFresh (nb083AlphaDummy000 A B C R) b
        (nb083_focused_notmem_0000 A B C R) dv_A_b (TEnvFresh.nil A.fv)))

/-- Checked nominal proof certificate identified upstream as `nb083_focused_refl_0001`. -/
@[expose]
noncomputable def nb083FocusedRefl0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) :
    TReflOn [((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)]
      A.fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0002 A B C R b c dv_A_b dv_A_c)

theorem nb083_focused_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy001 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb083_focused_notmem_0005 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy001 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb083_wpp_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083AlphaDummy001 A B C R) ∉ ((synCsep2 B C)).fv := by
  simpa only [nb083AlphaDummy001, fv_syn_csep2, Finset.mem_union, not_or] using
    (And.intro (nb083_focused_notmem_0004 A B C R) (nb083_focused_notmem_0005 A B C R))

theorem nb083_wpp_notmem_0003 (B : Class) (C : Class) (c : Var) (dv_B_c : c ∉ B.fv)
    (dv_C_c : c ∉ C.fv) : c ∉ ((synCsep2 B C)).fv := by
  simpa only [fv_syn_csep2, Finset.mem_union, not_or] using (And.intro dv_B_c dv_C_c)

theorem nb083_compact_envfresh_0003 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_B_b : b ∉ B.fv) (dv_B_c : c ∉ B.fv) (dv_C_b : b ∉ C.fv)
    (dv_C_c : c ∉ C.fv) :
    TEnvFresh [((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)]
      ((synCsep2 B C)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb083AlphaDummy001 A B C R) c (nb083_wpp_notmem_0002 A B C R)
      (nb083_wpp_notmem_0003 B C c dv_B_c dv_C_c)
      (TEnvFresh.consFresh (nb083AlphaDummy000 A B C R) b
        (nb083_wpp_notmem_0000 A B C R) (nb083_wpp_notmem_0001 B C b dv_B_b dv_C_b)
        (TEnvFresh.nil ((synCsep2 B C)).fv)))

/-- Checked nominal proof certificate identified upstream as `nb083_wpp_refl_0001`. -/
@[expose]
noncomputable def nb083WppRefl0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_B_b : b ∉ B.fv) (dv_B_c : c ∉ B.fv) (dv_C_b : b ∉ C.fv)
    (dv_C_c : c ∉ C.fv) :
    TReflOn [((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)]
      ((synCsep2 B C)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0003 A B C R b c dv_B_b dv_B_c dv_C_b dv_C_c)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
