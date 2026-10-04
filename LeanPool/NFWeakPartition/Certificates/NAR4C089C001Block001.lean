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

/-! Certificates from `NAR4C089C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_000`. -/
@[expose]
noncomputable def nb089AlphaDummy000 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_001`. -/
@[expose]
noncomputable def nb089AlphaDummy001 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synWbr R (synCwe) A)).fv ∪
        ((synCmpt (nb089AlphaDummy000 A B R) (synCpw1 (synCpw1 (synCuni A)))
            (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))).fv ∪ ((synC0)).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_002`. -/
@[expose]
noncomputable def nb089AlphaDummy002 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synWbr R (synCwe) A)).fv ∪ ((synCmpt u (synCpw1 (synCpw1 (synCuni A)))
            (synCfdrowfib R A B (Class.cv u)))).fv ∪ ((synC0)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_003`. -/
@[expose]
noncomputable def nb089AlphaDummy003 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
        ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
      ((synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_004`. -/
@[expose]
noncomputable def nb089AlphaDummy004 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
      ((synCfdrowfib R A B (Class.cv u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_005`. -/
@[expose]
noncomputable def nb089AlphaDummy005 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
        ({(nb089AlphaDummy003 A B R)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R))
            (synCpw1 (synCpw1 (synCuni A))))
          (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
            (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_006`. -/
@[expose]
noncomputable def nb089AlphaDummy006 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (({ u } : Finset Var) ∪ ({(nb089AlphaDummy004 u A B R)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
          (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
            (synCfdrowfib R A B (Class.cv u))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_007`. -/
@[expose]
noncomputable def nb089AlphaDummy007 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy003 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_008`. -/
@[expose]
noncomputable def nb089AlphaDummy008 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy003 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_009`. -/
@[expose]
noncomputable def nb089AlphaDummy009 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_010`. -/
@[expose]
noncomputable def nb089AlphaDummy010 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_011`. -/
@[expose]
noncomputable def nb089AlphaDummy011 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb089AlphaDummy007 A B R)
            (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCphi (Class.cv (nb089AlphaDummy008 A B R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_012`. -/
@[expose]
noncomputable def nb089AlphaDummy012 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb089AlphaDummy009 u A B R) (synWrex (nb089AlphaDummy010 u A B R)
              (Class.cv (nb089AlphaDummy004 u A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_013`. -/
@[expose]
noncomputable def nb089AlphaDummy013 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb089AlphaDummy007 A B R)
          (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy000 A B R))
            (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
              (synCphi (Class.cv (nb089AlphaDummy008 A B R))))))).fv ∪
      ((Class.cab (nb089AlphaDummy007 A B R)
          (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy000 A B R))
            (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
              (synCphi (Class.cv (nb089AlphaDummy008 A B R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_014`. -/
@[expose]
noncomputable def nb089AlphaDummy014 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb089AlphaDummy009 u A B R)
          (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
              (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))))).fv ∪
      ((Class.cab (nb089AlphaDummy009 u A B R)
          (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
              (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_015`. -/
@[expose]
noncomputable def nb089AlphaDummy015 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy008 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_016`. -/
@[expose]
noncomputable def nb089AlphaDummy016 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy008 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_017`. -/
@[expose]
noncomputable def nb089AlphaDummy017 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy010 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_018`. -/
@[expose]
noncomputable def nb089AlphaDummy018 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy010 u A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_019`. -/
@[expose]
noncomputable def nb089AlphaDummy019 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb089AlphaDummy015 A B R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb089AlphaDummy015 A B R)) (synC1c))).fv ∪
      ((Class.cv (nb089AlphaDummy015 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_020`. -/
@[expose]
noncomputable def nb089AlphaDummy020 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb089AlphaDummy017 u A B R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb089AlphaDummy017 u A B R)) (synC1c))).fv ∪
      ((Class.cv (nb089AlphaDummy017 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_021`. -/
@[expose]
noncomputable def nb089AlphaDummy021 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_022`. -/
@[expose]
noncomputable def nb089AlphaDummy022 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_023`. -/
@[expose]
noncomputable def nb089AlphaDummy023 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_024`. -/
@[expose]
noncomputable def nb089AlphaDummy024 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_025`. -/
@[expose]
noncomputable def nb089AlphaDummy025 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_026`. -/
@[expose]
noncomputable def nb089AlphaDummy026 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_027`. -/
@[expose]
noncomputable def nb089AlphaDummy027 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb089AlphaDummy022 A B R))
          (Class.cv (nb089AlphaDummy023 A B R)))).fv ∪
      ((synCnin (Class.cv (nb089AlphaDummy022 A B R))
          (Class.cv (nb089AlphaDummy023 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_028`. -/
@[expose]
noncomputable def nb089AlphaDummy028 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
          (Class.cv (nb089AlphaDummy026 u A B R)))).fv ∪
      ((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
          (Class.cv (nb089AlphaDummy026 u A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_029`. -/
@[expose]
noncomputable def nb089AlphaDummy029 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy023 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_030`. -/
@[expose]
noncomputable def nb089AlphaDummy030 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy026 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_031`. -/
@[expose]
noncomputable def nb089AlphaDummy031 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb089AlphaDummy022 A B R)))).fv ∪
      ((synCcompl (Class.cv (nb089AlphaDummy023 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_032`. -/
@[expose]
noncomputable def nb089AlphaDummy032 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb089AlphaDummy025 u A B R)))).fv ∪
      ((synCcompl (Class.cv (nb089AlphaDummy026 u A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_033`. -/
@[expose]
noncomputable def nb089AlphaDummy033 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy022 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_034`. -/
@[expose]
noncomputable def nb089AlphaDummy034 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy025 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_035`. -/
@[expose]
noncomputable def nb089AlphaDummy035 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy023 A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy023 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_036`. -/
@[expose]
noncomputable def nb089AlphaDummy036 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy026 u A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy026 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_037`. -/
@[expose]
noncomputable def nb089AlphaDummy037 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb089AlphaDummy007 A B R)
          (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy003 A B R))
            (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
              (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy007 A B R)
          (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy003 A B R))
            (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
              (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_038`. -/
@[expose]
noncomputable def nb089AlphaDummy038 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb089AlphaDummy009 u A B R)
          (synWrex (nb089AlphaDummy010 u A B R) (Class.cv (nb089AlphaDummy004 u A B R))
            (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
              (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy009 u A B R)
          (synWrex (nb089AlphaDummy010 u A B R) (Class.cv (nb089AlphaDummy004 u A B R))
            (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
              (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_039`. -/
@[expose]
noncomputable def nb089AlphaDummy039 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb089AlphaDummy008 A B R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_040`. -/
@[expose]
noncomputable def nb089AlphaDummy040 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_041`. -/
@[expose]
noncomputable def nb089AlphaDummy041 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb089AlphaDummy008 A B R)))).fv ∪
      ((synCphi (Class.cv (nb089AlphaDummy008 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_042`. -/
@[expose]
noncomputable def nb089AlphaDummy042 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb089AlphaDummy010 u A B R)))).fv ∪
      ((synCphi (Class.cv (nb089AlphaDummy010 u A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_043`. -/
@[expose]
noncomputable def nb089AlphaDummy043 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089AlphaDummy000 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_044`. -/
@[expose]
noncomputable def nb089AlphaDummy044 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_045`. -/
@[expose]
noncomputable def nb089AlphaDummy045 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
      ((Class.cv (nb089AlphaDummy000 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_046`. -/
@[expose]
noncomputable def nb089AlphaDummy046 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
      ((Class.cv (nb089AlphaDummy000 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_047`. -/
@[expose]
noncomputable def nb089AlphaDummy047 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_048`. -/
@[expose]
noncomputable def nb089AlphaDummy048 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_049`. -/
@[expose]
noncomputable def nb089AlphaDummy049 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb089AlphaDummy045 A B R)
            (synWrex (nb089AlphaDummy046 A B R)
              (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCphi (Class.cv (nb089AlphaDummy046 A B R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_050`. -/
@[expose]
noncomputable def nb089AlphaDummy050 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb089AlphaDummy047 u A B R)
            (synWrex (nb089AlphaDummy048 u A B R)
              (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb089AlphaDummy047 u A B R)
            (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_051`. -/
@[expose]
noncomputable def nb089AlphaDummy051 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
            (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
            (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
              (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))).fv ∪
      ((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
            (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
            (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
              (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_052`. -/
@[expose]
noncomputable def nb089AlphaDummy052 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb089AlphaDummy047 u A B R)
          (synWrex (nb089AlphaDummy048 u A B R)
            (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
            (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
              (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))).fv ∪
      ((Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
            (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
            (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
              (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_053`. -/
@[expose]
noncomputable def nb089AlphaDummy053 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy043 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_054`. -/
@[expose]
noncomputable def nb089AlphaDummy054 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy044 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_055`. -/
@[expose]
noncomputable def nb089AlphaDummy055 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy046 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_056`. -/
@[expose]
noncomputable def nb089AlphaDummy056 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy046 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_057`. -/
@[expose]
noncomputable def nb089AlphaDummy057 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy048 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_058`. -/
@[expose]
noncomputable def nb089AlphaDummy058 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy048 u A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_059`. -/
@[expose]
noncomputable def nb089AlphaDummy059 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb089AlphaDummy055 A B R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb089AlphaDummy055 A B R)) (synC1c))).fv ∪
      ((Class.cv (nb089AlphaDummy055 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_060`. -/
@[expose]
noncomputable def nb089AlphaDummy060 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb089AlphaDummy057 u A B R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb089AlphaDummy057 u A B R)) (synC1c))).fv ∪
      ((Class.cv (nb089AlphaDummy057 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_061`. -/
@[expose]
noncomputable def nb089AlphaDummy061 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_062`. -/
@[expose]
noncomputable def nb089AlphaDummy062 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_063`. -/
@[expose]
noncomputable def nb089AlphaDummy063 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_064`. -/
@[expose]
noncomputable def nb089AlphaDummy064 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_065`. -/
@[expose]
noncomputable def nb089AlphaDummy065 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_066`. -/
@[expose]
noncomputable def nb089AlphaDummy066 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_067`. -/
@[expose]
noncomputable def nb089AlphaDummy067 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb089AlphaDummy062 A B R))
          (Class.cv (nb089AlphaDummy063 A B R)))).fv ∪
      ((synCnin (Class.cv (nb089AlphaDummy062 A B R))
          (Class.cv (nb089AlphaDummy063 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_068`. -/
@[expose]
noncomputable def nb089AlphaDummy068 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
          (Class.cv (nb089AlphaDummy066 u A B R)))).fv ∪
      ((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
          (Class.cv (nb089AlphaDummy066 u A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_069`. -/
@[expose]
noncomputable def nb089AlphaDummy069 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy063 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_070`. -/
@[expose]
noncomputable def nb089AlphaDummy070 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy066 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_071`. -/
@[expose]
noncomputable def nb089AlphaDummy071 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb089AlphaDummy062 A B R)))).fv ∪
      ((synCcompl (Class.cv (nb089AlphaDummy063 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_072`. -/
@[expose]
noncomputable def nb089AlphaDummy072 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb089AlphaDummy065 u A B R)))).fv ∪
      ((synCcompl (Class.cv (nb089AlphaDummy066 u A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_073`. -/
@[expose]
noncomputable def nb089AlphaDummy073 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy062 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_074`. -/
@[expose]
noncomputable def nb089AlphaDummy074 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy065 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_075`. -/
@[expose]
noncomputable def nb089AlphaDummy075 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089AlphaDummy063 A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy063 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_076`. -/
@[expose]
noncomputable def nb089AlphaDummy076 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089AlphaDummy066 u A B R))).fv ∪
      ((Class.cv (nb089AlphaDummy066 u A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_077`. -/
@[expose]
noncomputable def nb089AlphaDummy077 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb089AlphaDummy045 A B R)
          (synWrex (nb089AlphaDummy046 A B R) (Class.cv (nb089AlphaDummy000 A B R))
            (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
              (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy045 A B R)
          (synWrex (nb089AlphaDummy046 A B R) (Class.cv (nb089AlphaDummy000 A B R))
            (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
              (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_078`. -/
@[expose]
noncomputable def nb089AlphaDummy078 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb089AlphaDummy047 u A B R)
          (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
              (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy047 u A B R)
          (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
              (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_079`. -/
@[expose]
noncomputable def nb089AlphaDummy079 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb089AlphaDummy046 A B R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_080`. -/
@[expose]
noncomputable def nb089AlphaDummy080 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_081`. -/
@[expose]
noncomputable def nb089AlphaDummy081 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb089AlphaDummy046 A B R)))).fv ∪
      ((synCphi (Class.cv (nb089AlphaDummy046 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb089_alpha_dummy_082`. -/
@[expose]
noncomputable def nb089AlphaDummy082 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb089AlphaDummy048 u A B R)))).fv ∪
      ((synCphi (Class.cv (nb089AlphaDummy048 u A B R)))).fv) 0)

theorem nb089_fresh_000 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy013 A B R) ∉
      (((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCphi (Class.cv (nb089AlphaDummy008 A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCphi (Class.cv (nb089AlphaDummy008 A B R))))))).fv) :=
  by
  simpa only [nb089AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCphi (Class.cv (nb089AlphaDummy008 A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCphi (Class.cv (nb089AlphaDummy008 A B R))))))).fv)
      0

theorem nb089_fresh_001 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy037 A B R) ∉
      (((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy007 A B R)
            (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb089AlphaDummy037] using
    freshVar_not_mem
      (((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy007 A B R)
            (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb089_fresh_002 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy038 u A B R) ∉
      (((Class.cab (nb089AlphaDummy009 u A B R) (synWrex (nb089AlphaDummy010 u A B R)
              (Class.cv (nb089AlphaDummy004 u A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv (nb089AlphaDummy004 u A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb089AlphaDummy038] using
    freshVar_not_mem
      (((Class.cab (nb089AlphaDummy009 u A B R) (synWrex (nb089AlphaDummy010 u A B R)
              (Class.cv (nb089AlphaDummy004 u A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv (nb089AlphaDummy004 u A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb089_fresh_003 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy014 u A B R) ∉
      (((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))))).fv) :=
  by
  simpa only [nb089AlphaDummy014] using
    freshVar_not_mem
      (((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))))).fv)
      0

theorem nb089_fresh_004 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy077 A B R) ∉
      (((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy045 A B R)
            (synWrex (nb089AlphaDummy046 A B R) (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb089AlphaDummy077] using
    freshVar_not_mem
      (((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy045 A B R)
            (synWrex (nb089AlphaDummy046 A B R) (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb089_fresh_005 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy051 A B R) ∉
      (((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))).fv) :=
  by
  simpa only [nb089AlphaDummy051] using
    freshVar_not_mem
      (((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))).fv)
      0

theorem nb089_fresh_006 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy078 u A B R) ∉
      (((Class.cab (nb089AlphaDummy047 u A B R)
            (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy047 u A B R)
            (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb089AlphaDummy078] using
    freshVar_not_mem
      (((Class.cab (nb089AlphaDummy047 u A B R)
            (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy047 u A B R)
            (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb089_fresh_007 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy052 u A B R) ∉
      (((Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
              (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
              (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))).fv) :=
  by
  simpa only [nb089AlphaDummy052] using
    freshVar_not_mem
      (((Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
              (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
              (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))).fv)
      0

theorem nb089_fresh_008 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy007 A B R) ∉
      (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy003 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy003 A B R))).fv)
      0

theorem nb089_fresh_009 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy008 A B R) ∉
      (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy003 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy008] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy003 A B R))).fv)
      1

theorem nb089_distinct_010 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy007 A B R) ≠ (nb089AlphaDummy008 A B R) := by
  simpa only [nb089AlphaDummy007, nb089AlphaDummy008] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy003 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_011 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy015 A B R) ∉ (((Class.cv (nb089AlphaDummy008 A B R))).fv) := by
  simpa only [nb089AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy008 A B R))).fv) 0

theorem nb089_fresh_012 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy016 A B R) ∉ (((Class.cv (nb089AlphaDummy008 A B R))).fv) := by
  simpa only [nb089AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy008 A B R))).fv) 1

theorem nb089_distinct_013 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy016 A B R) := by
  simpa only [nb089AlphaDummy015, nb089AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy008 A B R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb089_fresh_014 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy017 u A B R) ∉ (((Class.cv (nb089AlphaDummy010 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy010 u A B R))).fv) 0

theorem nb089_fresh_015 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy018 u A B R) ∉ (((Class.cv (nb089AlphaDummy010 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy010 u A B R))).fv) 1

theorem nb089_distinct_016 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy018 u A B R) := by
  simpa only [nb089AlphaDummy017, nb089AlphaDummy018] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy010 u A B R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb089_fresh_017 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy021 A B R) ∉
      (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) 0

theorem nb089_fresh_018 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy022 A B R) ∉
      (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) 1

theorem nb089_fresh_019 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy023 A B R) ∉
      (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) 2

theorem nb089_distinct_020 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy021 A B R) ≠ (nb089AlphaDummy022 A B R) := by
  simpa only [nb089AlphaDummy021, nb089AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_distinct_021 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy021 A B R) ≠ (nb089AlphaDummy023 A B R) := by
  simpa only [nb089AlphaDummy021, nb089AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb089_distinct_022 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy023 A B R) := by
  simpa only [nb089AlphaDummy022, nb089AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb089_fresh_023 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy024 u A B R) ∉
      (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) 0

theorem nb089_fresh_024 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy025 u A B R) ∉
      (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) 1

theorem nb089_fresh_025 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy026 u A B R) ∉
      (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) 2

theorem nb089_distinct_026 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy024 u A B R) ≠ (nb089AlphaDummy025 u A B R) := by
  simpa only [nb089AlphaDummy024, nb089AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_distinct_027 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy024 u A B R) ≠ (nb089AlphaDummy026 u A B R) := by
  simpa only [nb089AlphaDummy024, nb089AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb089_distinct_028 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy026 u A B R) := by
  simpa only [nb089AlphaDummy025, nb089AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb089_fresh_029 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy033 A B R) ∉
      (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy022 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy022 A B R))).fv)
      0

theorem nb089_fresh_030 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy029 A B R) ∉
      (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy023 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy023 A B R))).fv)
      0

theorem nb089_fresh_031 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy035 A B R) ∉
      (((Class.cv (nb089AlphaDummy023 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy023 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy023 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy023 A B R))).fv)
      0

theorem nb089_fresh_032 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy034 u A B R) ∉
      (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy025 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy025 u A B R))).fv)
      0

theorem nb089_fresh_033 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy030 u A B R) ∉
      (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy026 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy026 u A B R))).fv)
      0

theorem nb089_fresh_034 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy036 u A B R) ∉
      (((Class.cv (nb089AlphaDummy026 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy026 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy026 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy026 u A B R))).fv)
      0

theorem nb089_fresh_035 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy053 A B R) ∉ (((Class.cv (nb089AlphaDummy043 A B R))).fv) := by
  simpa only [nb089AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy043 A B R))).fv) 0

theorem nb089_fresh_036 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy054 u A B R) ∉ (((Class.cv (nb089AlphaDummy044 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy054] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy044 u A B R))).fv) 0

theorem nb089_fresh_037 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy055 A B R) ∉ (((Class.cv (nb089AlphaDummy046 A B R))).fv) := by
  simpa only [nb089AlphaDummy055] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy046 A B R))).fv) 0

theorem nb089_fresh_038 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy056 A B R) ∉ (((Class.cv (nb089AlphaDummy046 A B R))).fv) := by
  simpa only [nb089AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy046 A B R))).fv) 1

theorem nb089_distinct_039 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy055 A B R) ≠ (nb089AlphaDummy056 A B R) := by
  simpa only [nb089AlphaDummy055, nb089AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy046 A B R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb089_fresh_040 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy057 u A B R) ∉ (((Class.cv (nb089AlphaDummy048 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy048 u A B R))).fv) 0

theorem nb089_fresh_041 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy058 u A B R) ∉ (((Class.cv (nb089AlphaDummy048 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy048 u A B R))).fv) 1

theorem nb089_distinct_042 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy058 u A B R) := by
  simpa only [nb089AlphaDummy057, nb089AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy048 u A B R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb089_fresh_043 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy061 A B R) ∉
      (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) 0

theorem nb089_fresh_044 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy062 A B R) ∉
      (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) 1

theorem nb089_fresh_045 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy063 A B R) ∉
      (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) 2

theorem nb089_distinct_046 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy061 A B R) ≠ (nb089AlphaDummy062 A B R) := by
  simpa only [nb089AlphaDummy061, nb089AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_distinct_047 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy061 A B R) ≠ (nb089AlphaDummy063 A B R) := by
  simpa only [nb089AlphaDummy061, nb089AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb089_distinct_048 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy063 A B R) := by
  simpa only [nb089AlphaDummy062, nb089AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb089_fresh_049 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy064 u A B R) ∉
      (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) 0

theorem nb089_fresh_050 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy065 u A B R) ∉
      (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy065] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) 1

theorem nb089_fresh_051 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy066 u A B R) ∉
      (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb089AlphaDummy066] using
    freshVar_not_mem (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) 2

theorem nb089_distinct_052 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy064 u A B R) ≠ (nb089AlphaDummy065 u A B R) := by
  simpa only [nb089AlphaDummy064, nb089AlphaDummy065] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_distinct_053 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy064 u A B R) ≠ (nb089AlphaDummy066 u A B R) := by
  simpa only [nb089AlphaDummy064, nb089AlphaDummy066] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb089_distinct_054 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy066 u A B R) := by
  simpa only [nb089AlphaDummy065, nb089AlphaDummy066] using
    (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb089_fresh_055 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy073 A B R) ∉
      (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy062 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy073] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy062 A B R))).fv)
      0

theorem nb089_fresh_056 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy069 A B R) ∉
      (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy063 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy063 A B R))).fv)
      0

theorem nb089_fresh_057 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy075 A B R) ∉
      (((Class.cv (nb089AlphaDummy063 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy063 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy075] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy063 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy063 A B R))).fv)
      0

theorem nb089_fresh_058 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy074 u A B R) ∉
      (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy065 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy074] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy065 u A B R))).fv)
      0

theorem nb089_fresh_059 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy070 u A B R) ∉
      (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy066 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy066 u A B R))).fv)
      0

theorem nb089_fresh_060 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy076 u A B R) ∉
      (((Class.cv (nb089AlphaDummy066 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy066 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy076] using
    freshVar_not_mem
      (((Class.cv (nb089AlphaDummy066 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy066 u A B R))).fv)
      0

theorem nb089_fresh_061 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy009 u A B R) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy009] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv)
      0

theorem nb089_fresh_062 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy010 u A B R) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy010] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv)
      1

theorem nb089_distinct_063 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy009 u A B R) ≠ (nb089AlphaDummy010 u A B R) := by
  simpa only [nb089AlphaDummy009, nb089AlphaDummy010] using
    (freshVar_injective
      (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb089_fresh_064 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy019 A B R) ∉
      (((Wff.classMem (Class.cv (nb089AlphaDummy015 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy015 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy015 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb089AlphaDummy015 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy015 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy015 A B R))).fv)
      0

theorem nb089_fresh_065 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy020 u A B R) ∉
      (((Wff.classMem (Class.cv (nb089AlphaDummy017 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy017 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy017 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb089AlphaDummy017 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy017 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy017 u A B R))).fv)
      0

theorem nb089_fresh_066 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy059 A B R) ∉
      (((Wff.classMem (Class.cv (nb089AlphaDummy055 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy055 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy055 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy059] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb089AlphaDummy055 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy055 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy055 A B R))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C089C001Part002`. -/


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

theorem nb089_fresh_067 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy060 u A B R) ∉
      (((Wff.classMem (Class.cv (nb089AlphaDummy057 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy057 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy057 u A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy060] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb089AlphaDummy057 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy057 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy057 u A B R))).fv)
      0

theorem nb089_fresh_068 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy011 A B R) ∉
      (((synCcompl (Class.cab (nb089AlphaDummy007 A B R)
              (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy008 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
                (Class.cv (nb089AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb089AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb089AlphaDummy007 A B R)
              (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy008 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
                (Class.cv (nb089AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb089_fresh_069 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy012 u A B R) ∉
      (((synCcompl (Class.cab (nb089AlphaDummy009 u A B R)
              (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy009 u A B R) (synWrex (nb089AlphaDummy010 u A B R)
                (Class.cv (nb089AlphaDummy004 u A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb089AlphaDummy012] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb089AlphaDummy009 u A B R)
              (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy009 u A B R) (synWrex (nb089AlphaDummy010 u A B R)
                (Class.cv (nb089AlphaDummy004 u A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb089_fresh_070 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy049 A B R) ∉
      (((synCcompl (Class.cab (nb089AlphaDummy045 A B R)
              (synWrex (nb089AlphaDummy046 A B R)
                (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy046 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
                (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb089AlphaDummy049] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb089AlphaDummy045 A B R)
              (synWrex (nb089AlphaDummy046 A B R)
                (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy046 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
                (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb089_fresh_071 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy050 u A B R) ∉
      (((synCcompl (Class.cab (nb089AlphaDummy047 u A B R)
              (synWrex (nb089AlphaDummy048 u A B R)
                (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy047 u A B R)
              (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb089AlphaDummy050] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb089AlphaDummy047 u A B R)
              (synWrex (nb089AlphaDummy048 u A B R)
                (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy047 u A B R)
              (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb089_fresh_072 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy031 A B R) ∉
      (((synCcompl (Class.cv (nb089AlphaDummy022 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy023 A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy031] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb089AlphaDummy022 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy023 A B R)))).fv)
      0

theorem nb089_fresh_073 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy032 u A B R) ∉
      (((synCcompl (Class.cv (nb089AlphaDummy025 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy026 u A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy032] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb089AlphaDummy025 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy026 u A B R)))).fv)
      0

theorem nb089_fresh_074 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy071 A B R) ∉
      (((synCcompl (Class.cv (nb089AlphaDummy062 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy063 A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy071] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb089AlphaDummy062 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy063 A B R)))).fv)
      0

theorem nb089_fresh_075 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy072 u A B R) ∉
      (((synCcompl (Class.cv (nb089AlphaDummy065 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy066 u A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy072] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb089AlphaDummy065 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy066 u A B R)))).fv)
      0

theorem nb089_fresh_076 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy039 A B R) ∉
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy008 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb089AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy008 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb089_fresh_077 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy040 u A B R) ∉
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb089AlphaDummy040] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb089_fresh_078 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy079 A B R) ∉
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy046 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb089AlphaDummy079] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy046 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb089_fresh_079 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy080 u A B R) ∉
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb089AlphaDummy080] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb089_fresh_080 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy027 A B R) ∉
      (((synCnin (Class.cv (nb089AlphaDummy022 A B R))
            (Class.cv (nb089AlphaDummy023 A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy022 A B R))
            (Class.cv (nb089AlphaDummy023 A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy027] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb089AlphaDummy022 A B R))
            (Class.cv (nb089AlphaDummy023 A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy022 A B R))
            (Class.cv (nb089AlphaDummy023 A B R)))).fv)
      0

theorem nb089_fresh_081 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy028 u A B R) ∉
      (((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
            (Class.cv (nb089AlphaDummy026 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
            (Class.cv (nb089AlphaDummy026 u A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy028] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
            (Class.cv (nb089AlphaDummy026 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
            (Class.cv (nb089AlphaDummy026 u A B R)))).fv)
      0

theorem nb089_fresh_082 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy067 A B R) ∉
      (((synCnin (Class.cv (nb089AlphaDummy062 A B R))
            (Class.cv (nb089AlphaDummy063 A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy062 A B R))
            (Class.cv (nb089AlphaDummy063 A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy067] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb089AlphaDummy062 A B R))
            (Class.cv (nb089AlphaDummy063 A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy062 A B R))
            (Class.cv (nb089AlphaDummy063 A B R)))).fv)
      0

theorem nb089_fresh_083 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy068 u A B R) ∉
      (((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
            (Class.cv (nb089AlphaDummy066 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
            (Class.cv (nb089AlphaDummy066 u A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy068] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
            (Class.cv (nb089AlphaDummy066 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
            (Class.cv (nb089AlphaDummy066 u A B R)))).fv)
      0

theorem nb089_fresh_084 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy041 A B R) ∉
      (((synCphi (Class.cv (nb089AlphaDummy008 A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy008 A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy041] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb089AlphaDummy008 A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy008 A B R)))).fv)
      0

theorem nb089_fresh_085 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy042 u A B R) ∉
      (((synCphi (Class.cv (nb089AlphaDummy010 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy010 u A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy042] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb089AlphaDummy010 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy010 u A B R)))).fv)
      0

theorem nb089_fresh_086 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy081 A B R) ∉
      (((synCphi (Class.cv (nb089AlphaDummy046 A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy046 A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy081] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb089AlphaDummy046 A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy046 A B R)))).fv)
      0

theorem nb089_fresh_087 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy082 u A B R) ∉
      (((synCphi (Class.cv (nb089AlphaDummy048 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy048 u A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy082] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb089AlphaDummy048 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy048 u A B R)))).fv)
      0

theorem nb089_fresh_088 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy045 A B R) ∉
      (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
        ((Class.cv (nb089AlphaDummy000 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy045] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
        ((Class.cv (nb089AlphaDummy000 A B R))).fv)
      0

theorem nb089_fresh_089 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy046 A B R) ∉
      (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
        ((Class.cv (nb089AlphaDummy000 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy046] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
        ((Class.cv (nb089AlphaDummy000 A B R))).fv)
      1

theorem nb089_distinct_090 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy045 A B R) ≠ (nb089AlphaDummy046 A B R) := by
  simpa only [nb089AlphaDummy045, nb089AlphaDummy046] using
    (freshVar_injective (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
        ((Class.cv (nb089AlphaDummy000 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_091 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy047 u A B R) ∉
      (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  simpa only [nb089AlphaDummy047] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv) 0

theorem nb089_fresh_092 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy048 u A B R) ∉
      (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  simpa only [nb089AlphaDummy048] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv) 1

theorem nb089_distinct_093 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy047 u A B R) ≠ (nb089AlphaDummy048 u A B R) := by
  simpa only [nb089AlphaDummy047, nb089AlphaDummy048] using
    (freshVar_injective
      (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_fresh_094 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉
      (((synWbr R (synCwe) A)).fv ∪
          ((synCmpt (nb089AlphaDummy000 A B R) (synCpw1 (synCpw1 (synCuni A)))
              (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))).fv ∪
        ((synC0)).fv) :=
  by
  simpa only [nb089AlphaDummy001] using
    freshVar_not_mem
      (((synWbr R (synCwe) A)).fv ∪
          ((synCmpt (nb089AlphaDummy000 A B R) (synCpw1 (synCpw1 (synCuni A)))
              (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))).fv ∪
        ((synC0)).fv)
      0

theorem nb089_fresh_095 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy002 u A B R) ∉
      (((synWbr R (synCwe) A)).fv ∪ ((synCmpt u (synCpw1 (synCpw1 (synCuni A)))
              (synCfdrowfib R A B (Class.cv u)))).fv ∪ ((synC0)).fv) :=
  by
  simpa only [nb089AlphaDummy002] using
    freshVar_not_mem
      (((synWbr R (synCwe) A)).fv ∪ ((synCmpt u (synCpw1 (synCpw1 (synCuni A)))
              (synCfdrowfib R A B (Class.cv u)))).fv ∪ ((synC0)).fv)
      0

theorem nb089_fresh_096 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb089AlphaDummy000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb089_fresh_097 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∉
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089AlphaDummy000 A B R))).fv) :=
  by
  simpa only [nb089AlphaDummy043] using
    freshVar_not_mem
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089AlphaDummy000 A B R))).fv) 0

theorem nb089_fresh_098 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb089AlphaDummy044] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0

theorem nb089_fresh_099 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∉
      (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
          ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
        ((synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))).fv) :=
  by
  simpa only [nb089AlphaDummy003] using
    freshVar_not_mem
      (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
          ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
        ((synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))).fv)
      0

theorem nb089_fresh_100 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy005 A B R) ∉
      (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
          ({(nb089AlphaDummy003 A B R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R))
              (synCpw1 (synCpw1 (synCuni A))))
            (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
              (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))))).fv) :=
  by
  simpa only [nb089AlphaDummy005] using
    freshVar_not_mem
      (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
          ({(nb089AlphaDummy003 A B R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R))
              (synCpw1 (synCpw1 (synCuni A))))
            (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
              (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))))).fv)
      0

theorem nb089_fresh_101 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∉
      (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
        ((synCfdrowfib R A B (Class.cv u))).fv) :=
  by
  simpa only [nb089AlphaDummy004] using
    freshVar_not_mem
      (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
        ((synCfdrowfib R A B (Class.cv u))).fv)
      0

theorem nb089_fresh_102 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy006 u A B R) ∉
      (({ u } : Finset Var) ∪ ({(nb089AlphaDummy004 u A B R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
            (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
              (synCfdrowfib R A B (Class.cv u))))).fv) :=
  by
  simpa only [nb089AlphaDummy006] using
    freshVar_not_mem
      (({ u } : Finset Var) ∪ ({(nb089AlphaDummy004 u A B R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
            (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
              (synCfdrowfib R A B (Class.cv u))))).fv)
      0

theorem nb089_support_mem_0000 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
          ({(nb089AlphaDummy003 A B R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R))
              (synCpw1 (synCpw1 (synCuni A))))
            (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
              (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0001 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (({ u } : Finset Var) ∪ ({(nb089AlphaDummy004 u A B R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
            (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
              (synCfdrowfib R A B (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0002 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∈
      (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
          ({(nb089AlphaDummy003 A B R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R))
              (synCpw1 (synCpw1 (synCuni A))))
            (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
              (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0003 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∈
      (({ u } : Finset Var) ∪ ({(nb089AlphaDummy004 u A B R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
            (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
              (synCfdrowfib R A B (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0004 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
          ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
        ((synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0005 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
        ((synCfdrowfib R A B (Class.cv u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0006 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy003 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0007 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      (((synCcompl (Class.cab (nb089AlphaDummy007 A B R)
              (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy008 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
                (Class.cv (nb089AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy007 A B R) from (by
          unfold nb089AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy008 A B R) from (by
            unfold nb089AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0008 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0009 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((synCcompl (Class.cab (nb089AlphaDummy009 u A B R)
              (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy009 u A B R) (synWrex (nb089AlphaDummy010 u A B R)
                (Class.cv (nb089AlphaDummy004 u A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb089AlphaDummy009 u A B R) from (by
          unfold nb089AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb089AlphaDummy010 u A B R) from (by
            unfold nb089AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0010 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      (((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCphi (Class.cv (nb089AlphaDummy008 A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCphi (Class.cv (nb089AlphaDummy008 A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy007 A B R) from (by
          unfold nb089AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy008 A B R) from (by
            unfold nb089AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0011 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb089AlphaDummy009 u A B R) from (by
          unfold nb089AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb089AlphaDummy010 u A B R) from (by
            unfold nb089AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0012 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy008 A B R) ∈ (((Class.cv (nb089AlphaDummy008 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0013 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy010 u A B R) ∈ (((Class.cv (nb089AlphaDummy010 u A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0014 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy015 A B R) ∈
      (((Wff.classMem (Class.cv (nb089AlphaDummy015 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy015 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy015 A B R))).fv) :=
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

theorem nb089_support_mem_0015 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy017 u A B R) ∈
      (((Wff.classMem (Class.cv (nb089AlphaDummy017 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy017 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy017 u A B R))).fv) :=
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

theorem nb089_support_mem_0016 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy015 A B R) ∈
      (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0017 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy017 u A B R) ∈
      (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0018 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy022 A B R) ∈
      (((synCnin (Class.cv (nb089AlphaDummy022 A B R))
            (Class.cv (nb089AlphaDummy023 A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy022 A B R))
            (Class.cv (nb089AlphaDummy023 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0019 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy025 u A B R) ∈
      (((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
            (Class.cv (nb089AlphaDummy026 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
            (Class.cv (nb089AlphaDummy026 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0020 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy022 A B R) ∈
      (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy023 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0021 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy025 u A B R) ∈
      (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy026 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0022 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy023 A B R) ∈
      (((synCnin (Class.cv (nb089AlphaDummy022 A B R))
            (Class.cv (nb089AlphaDummy023 A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy022 A B R))
            (Class.cv (nb089AlphaDummy023 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0023 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy026 u A B R) ∈
      (((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
            (Class.cv (nb089AlphaDummy026 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy025 u A B R))
            (Class.cv (nb089AlphaDummy026 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0024 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy023 A B R) ∈
      (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy023 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0025 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy026 u A B R) ∈
      (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy026 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0026 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy022 A B R) ∈
      (((synCcompl (Class.cv (nb089AlphaDummy022 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy023 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0027 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy025 u A B R) ∈
      (((synCcompl (Class.cv (nb089AlphaDummy025 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy026 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0028 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy022 A B R) ∈
      (((Class.cv (nb089AlphaDummy022 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy022 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0029 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy025 u A B R) ∈
      (((Class.cv (nb089AlphaDummy025 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy025 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0030 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy023 A B R) ∈
      (((synCcompl (Class.cv (nb089AlphaDummy022 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy023 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0031 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy026 u A B R) ∈
      (((synCcompl (Class.cv (nb089AlphaDummy025 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy026 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0032 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy023 A B R) ∈
      (((Class.cv (nb089AlphaDummy023 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy023 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0033 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy026 u A B R) ∈
      (((Class.cv (nb089AlphaDummy026 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy026 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0034 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∈
      (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy003 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0035 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∈
      (((synCcompl (Class.cab (nb089AlphaDummy007 A B R)
              (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy008 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
                (Class.cv (nb089AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy003 A B R) ≠ (nb089AlphaDummy007 A B R) from (by
          unfold nb089AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy003 A B R) ≠ (nb089AlphaDummy008 A B R) from (by
            unfold nb089AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0036 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∈
      (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0037 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∈
      (((synCcompl (Class.cab (nb089AlphaDummy009 u A B R)
              (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy009 u A B R) (synWrex (nb089AlphaDummy010 u A B R)
                (Class.cv (nb089AlphaDummy004 u A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy004 u A B R) ≠ (nb089AlphaDummy009 u A B R) from (by
          unfold nb089AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy004 u A B R) ≠ (nb089AlphaDummy010 u A B R) from (by
            unfold nb089AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0038 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∈
      (((Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
              (Class.cv (nb089AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy007 A B R)
            (synWrex (nb089AlphaDummy008 A B R) (Class.cv (nb089AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy003 A B R) ≠ (nb089AlphaDummy007 A B R) from (by
          unfold nb089AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy003 A B R) ≠ (nb089AlphaDummy008 A B R) from (by
            unfold nb089AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0039 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∈
      (((Class.cab (nb089AlphaDummy009 u A B R) (synWrex (nb089AlphaDummy010 u A B R)
              (Class.cv (nb089AlphaDummy004 u A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy009 u A B R)
            (synWrex (nb089AlphaDummy010 u A B R) (Class.cv (nb089AlphaDummy004 u A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy004 u A B R) ≠ (nb089AlphaDummy009 u A B R) from (by
          unfold nb089AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy004 u A B R) ≠ (nb089AlphaDummy010 u A B R) from (by
            unfold nb089AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0040 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy008 A B R) ∈
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy008 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0041 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy010 u A B R) ∈
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy010 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0042 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy008 A B R) ∈
      (((synCphi (Class.cv (nb089AlphaDummy008 A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy008 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0043 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy010 u A B R) ∈
      (((synCphi (Class.cv (nb089AlphaDummy010 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy010 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0044 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∈
      (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
        ((Class.cv (nb089AlphaDummy000 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0045 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∈
      (((synCcompl (Class.cab (nb089AlphaDummy045 A B R)
              (synWrex (nb089AlphaDummy046 A B R)
                (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy046 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
                (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy045 A B R) from (by
          unfold nb089AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy046 A B R) from (by
            unfold nb089AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0046 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∈
      (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0047 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∈
      (((synCcompl (Class.cab (nb089AlphaDummy047 u A B R)
              (synWrex (nb089AlphaDummy048 u A B R)
                (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy047 u A B R)
              (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy047 u A B R) from (by
          unfold nb089AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy048 u A B R) from (by
            unfold nb089AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0048 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∈
      (((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy045 A B R) from (by
          unfold nb089AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy046 A B R) from (by
            unfold nb089AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0049 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∈
      (((Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
              (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))).fv ∪
        ((Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
              (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy047 u A B R) from (by
          unfold nb089AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy048 u A B R) from (by
            unfold nb089AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0050 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∈ (((Class.cv (nb089AlphaDummy043 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0051 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∈ (((Class.cv (nb089AlphaDummy044 u A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0052 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy046 A B R) ∈ (((Class.cv (nb089AlphaDummy046 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0053 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy048 u A B R) ∈ (((Class.cv (nb089AlphaDummy048 u A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0054 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy055 A B R) ∈
      (((Wff.classMem (Class.cv (nb089AlphaDummy055 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy055 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy055 A B R))).fv) :=
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

theorem nb089_support_mem_0055 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy057 u A B R) ∈
      (((Wff.classMem (Class.cv (nb089AlphaDummy057 u A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb089AlphaDummy057 u A B R)) (synC1c))).fv ∪
        ((Class.cv (nb089AlphaDummy057 u A B R))).fv) :=
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

theorem nb089_support_mem_0056 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy055 A B R) ∈
      (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0057 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy057 u A B R) ∈
      (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0058 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy062 A B R) ∈
      (((synCnin (Class.cv (nb089AlphaDummy062 A B R))
            (Class.cv (nb089AlphaDummy063 A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy062 A B R))
            (Class.cv (nb089AlphaDummy063 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0059 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy065 u A B R) ∈
      (((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
            (Class.cv (nb089AlphaDummy066 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
            (Class.cv (nb089AlphaDummy066 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0060 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy062 A B R) ∈
      (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy063 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0061 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy065 u A B R) ∈
      (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy066 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0062 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy063 A B R) ∈
      (((synCnin (Class.cv (nb089AlphaDummy062 A B R))
            (Class.cv (nb089AlphaDummy063 A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy062 A B R))
            (Class.cv (nb089AlphaDummy063 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0063 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy066 u A B R) ∈
      (((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
            (Class.cv (nb089AlphaDummy066 u A B R)))).fv ∪
        ((synCnin (Class.cv (nb089AlphaDummy065 u A B R))
            (Class.cv (nb089AlphaDummy066 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0064 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy063 A B R) ∈
      (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy063 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0065 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy066 u A B R) ∈
      (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy066 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0066 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy062 A B R) ∈
      (((synCcompl (Class.cv (nb089AlphaDummy062 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy063 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0067 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy065 u A B R) ∈
      (((synCcompl (Class.cv (nb089AlphaDummy065 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy066 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0068 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy062 A B R) ∈
      (((Class.cv (nb089AlphaDummy062 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy062 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0069 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy065 u A B R) ∈
      (((Class.cv (nb089AlphaDummy065 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy065 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0070 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy063 A B R) ∈
      (((synCcompl (Class.cv (nb089AlphaDummy062 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy063 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0071 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy066 u A B R) ∈
      (((synCcompl (Class.cv (nb089AlphaDummy065 u A B R)))).fv ∪
        ((synCcompl (Class.cv (nb089AlphaDummy066 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0072 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy063 A B R) ∈
      (((Class.cv (nb089AlphaDummy063 A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy063 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0073 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy066 u A B R) ∈
      (((Class.cv (nb089AlphaDummy066 u A B R))).fv ∪
        ((Class.cv (nb089AlphaDummy066 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0074 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089AlphaDummy000 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0075 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0076 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
        ((Class.cv (nb089AlphaDummy000 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0077 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      (((synCcompl (Class.cab (nb089AlphaDummy045 A B R)
              (synWrex (nb089AlphaDummy046 A B R)
                (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy046 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
                (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy045 A B R) from (by
          unfold nb089AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy046 A B R) from (by
            unfold nb089AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0078 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈ (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0079 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((synCcompl (Class.cab (nb089AlphaDummy047 u A B R)
              (synWrex (nb089AlphaDummy048 u A B R)
                (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb089AlphaDummy047 u A B R)
              (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb089AlphaDummy047 u A B R) from (by
          unfold nb089AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb089AlphaDummy048 u A B R) from (by
            unfold nb089AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0080 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∈
      (((Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy045 A B R)
            (synWrex (nb089AlphaDummy046 A B R) (Class.cv (nb089AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy045 A B R) from (by
          unfold nb089AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy046 A B R) from (by
            unfold nb089AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0081 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((Class.cab (nb089AlphaDummy047 u A B R)
            (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb089AlphaDummy047 u A B R)
            (synWrex (nb089AlphaDummy048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb089AlphaDummy047 u A B R) from (by
          unfold nb089AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb089AlphaDummy048 u A B R) from (by
            unfold nb089AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0082 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy046 A B R) ∈
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy046 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0083 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy048 u A B R) ∈
      (((synCcompl (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0084 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy046 A B R) ∈
      (((synCphi (Class.cv (nb089AlphaDummy046 A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy046 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0085 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy048 u A B R) ∈
      (((synCphi (Class.cv (nb089AlphaDummy048 u A B R)))).fv ∪
        ((synCphi (Class.cv (nb089AlphaDummy048 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C089C001Part003`. -/


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

theorem nb089_compact_fv_empty_0026 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb089_compact_fv_empty_0027 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy002 u A B R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
