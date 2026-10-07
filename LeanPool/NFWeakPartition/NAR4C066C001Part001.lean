/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C066C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_000`. -/
@[expose]
noncomputable def nb066AlphaDummy000 (A : Class) (R : Class) : Var :=
  (freshVar ((A).fv ∪ (R).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_001`. -/
@[expose]
noncomputable def nb066AlphaDummy001 (A : Class) (R : Class) : Var :=
  (freshVar ((A).fv ∪ (R).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_002`. -/
@[expose]
noncomputable def nb066AlphaDummy002 (A : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((synCsn (Class.cv (nb066AlphaDummy000 A R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_003`. -/
@[expose]
noncomputable def nb066AlphaDummy003 (A : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((synCsn (Class.cv (nb066AlphaDummy000 A R)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_004`. -/
@[expose]
noncomputable def nb066AlphaDummy004 (x : Var) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((synCsn (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_005`. -/
@[expose]
noncomputable def nb066AlphaDummy005 (x : Var) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((synCsn (Class.cv x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_006`. -/
@[expose]
noncomputable def nb066AlphaDummy006 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy000 A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_007`. -/
@[expose]
noncomputable def nb066AlphaDummy007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_008`. -/
@[expose]
noncomputable def nb066AlphaDummy008 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
      ((Class.cv (nb066AlphaDummy002 A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_009`. -/
@[expose]
noncomputable def nb066AlphaDummy009 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
      ((Class.cv (nb066AlphaDummy002 A R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_010`. -/
@[expose]
noncomputable def nb066AlphaDummy010 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
      ((Class.cv (nb066AlphaDummy004 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_011`. -/
@[expose]
noncomputable def nb066AlphaDummy011 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
      ((Class.cv (nb066AlphaDummy004 x R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_012`. -/
@[expose]
noncomputable def nb066AlphaDummy012 (A : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCphi (Class.cv (nb066AlphaDummy009 A R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_013`. -/
@[expose]
noncomputable def nb066AlphaDummy013 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCphi (Class.cv (nb066AlphaDummy011 x R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_014`. -/
@[expose]
noncomputable def nb066AlphaDummy014 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb066AlphaDummy008 A R)
          (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
            (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
              (synCphi (Class.cv (nb066AlphaDummy009 A R))))))).fv ∪
      ((Class.cab (nb066AlphaDummy008 A R)
          (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
            (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
              (synCphi (Class.cv (nb066AlphaDummy009 A R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_015`. -/
@[expose]
noncomputable def nb066AlphaDummy015 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cab (nb066AlphaDummy010 x R)
          (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
            (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
              (synCphi (Class.cv (nb066AlphaDummy011 x R))))))).fv ∪
      ((Class.cab (nb066AlphaDummy010 x R)
          (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
            (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
              (synCphi (Class.cv (nb066AlphaDummy011 x R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_016`. -/
@[expose]
noncomputable def nb066AlphaDummy016 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy009 A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_017`. -/
@[expose]
noncomputable def nb066AlphaDummy017 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy009 A R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_018`. -/
@[expose]
noncomputable def nb066AlphaDummy018 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy011 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_019`. -/
@[expose]
noncomputable def nb066AlphaDummy019 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy011 x R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_020`. -/
@[expose]
noncomputable def nb066AlphaDummy020 (A : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb066AlphaDummy016 A R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb066AlphaDummy016 A R)) (synC1c))).fv ∪
      ((Class.cv (nb066AlphaDummy016 A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_021`. -/
@[expose]
noncomputable def nb066AlphaDummy021 (x : Var) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb066AlphaDummy018 x R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb066AlphaDummy018 x R)) (synC1c))).fv ∪
      ((Class.cv (nb066AlphaDummy018 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_022`. -/
@[expose]
noncomputable def nb066AlphaDummy022 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_023`. -/
@[expose]
noncomputable def nb066AlphaDummy023 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_024`. -/
@[expose]
noncomputable def nb066AlphaDummy024 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_025`. -/
@[expose]
noncomputable def nb066AlphaDummy025 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_026`. -/
@[expose]
noncomputable def nb066AlphaDummy026 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_027`. -/
@[expose]
noncomputable def nb066AlphaDummy027 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_028`. -/
@[expose]
noncomputable def nb066AlphaDummy028 (A : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb066AlphaDummy023 A R))
          (Class.cv (nb066AlphaDummy024 A R)))).fv ∪
      ((synCnin (Class.cv (nb066AlphaDummy023 A R))
          (Class.cv (nb066AlphaDummy024 A R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_029`. -/
@[expose]
noncomputable def nb066AlphaDummy029 (x : Var) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb066AlphaDummy026 x R))
          (Class.cv (nb066AlphaDummy027 x R)))).fv ∪
      ((synCnin (Class.cv (nb066AlphaDummy026 x R))
          (Class.cv (nb066AlphaDummy027 x R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_030`. -/
@[expose]
noncomputable def nb066AlphaDummy030 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
      ((Class.cv (nb066AlphaDummy024 A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_031`. -/
@[expose]
noncomputable def nb066AlphaDummy031 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
      ((Class.cv (nb066AlphaDummy027 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_032`. -/
@[expose]
noncomputable def nb066AlphaDummy032 (A : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb066AlphaDummy023 A R)))).fv ∪
      ((synCcompl (Class.cv (nb066AlphaDummy024 A R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_033`. -/
@[expose]
noncomputable def nb066AlphaDummy033 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb066AlphaDummy026 x R)))).fv ∪
      ((synCcompl (Class.cv (nb066AlphaDummy027 x R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_034`. -/
@[expose]
noncomputable def nb066AlphaDummy034 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
      ((Class.cv (nb066AlphaDummy023 A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_035`. -/
@[expose]
noncomputable def nb066AlphaDummy035 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
      ((Class.cv (nb066AlphaDummy026 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_036`. -/
@[expose]
noncomputable def nb066AlphaDummy036 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy024 A R))).fv ∪
      ((Class.cv (nb066AlphaDummy024 A R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_037`. -/
@[expose]
noncomputable def nb066AlphaDummy037 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb066AlphaDummy027 x R))).fv ∪
      ((Class.cv (nb066AlphaDummy027 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_038`. -/
@[expose]
noncomputable def nb066AlphaDummy038 (A : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb066AlphaDummy008 A R)
          (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
            (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
              (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb066AlphaDummy008 A R)
          (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
            (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
              (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_039`. -/
@[expose]
noncomputable def nb066AlphaDummy039 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cab (nb066AlphaDummy010 x R)
          (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
            (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
              (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb066AlphaDummy010 x R)
          (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
            (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
              (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_040`. -/
@[expose]
noncomputable def nb066AlphaDummy040 (A : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb066AlphaDummy009 A R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_041`. -/
@[expose]
noncomputable def nb066AlphaDummy041 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb066AlphaDummy011 x R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_042`. -/
@[expose]
noncomputable def nb066AlphaDummy042 (A : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb066AlphaDummy009 A R)))).fv ∪
      ((synCphi (Class.cv (nb066AlphaDummy009 A R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_043`. -/
@[expose]
noncomputable def nb066AlphaDummy043 (x : Var) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb066AlphaDummy011 x R)))).fv ∪
      ((synCphi (Class.cv (nb066AlphaDummy011 x R)))).fv) 0)

theorem nb066_fresh_000 (A : Class) (R : Class) :
    (nb066AlphaDummy038 A R) ∉
      (((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb066AlphaDummy038] using
    freshVar_not_mem
      (((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb066_fresh_001 (A : Class) (R : Class) :
    (nb066AlphaDummy014 A R) ∉
      (((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCphi (Class.cv (nb066AlphaDummy009 A R))))))).fv ∪
        ((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCphi (Class.cv (nb066AlphaDummy009 A R))))))).fv) :=
  by
  simpa only [nb066AlphaDummy014] using
    freshVar_not_mem
      (((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCphi (Class.cv (nb066AlphaDummy009 A R))))))).fv ∪
        ((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCphi (Class.cv (nb066AlphaDummy009 A R))))))).fv)
      0

theorem nb066_fresh_002 (x : Var) (R : Class) :
    (nb066AlphaDummy039 x R) ∉
      (((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb066AlphaDummy039] using
    freshVar_not_mem
      (((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb066_fresh_003 (x : Var) (R : Class) :
    (nb066AlphaDummy015 x R) ∉
      (((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCphi (Class.cv (nb066AlphaDummy011 x R))))))).fv ∪
        ((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCphi (Class.cv (nb066AlphaDummy011 x R))))))).fv) :=
  by
  simpa only [nb066AlphaDummy015] using
    freshVar_not_mem
      (((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCphi (Class.cv (nb066AlphaDummy011 x R))))))).fv ∪
        ((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCphi (Class.cv (nb066AlphaDummy011 x R))))))).fv)
      0

theorem nb066_fresh_004 (A : Class) (R : Class) :
    (nb066AlphaDummy006 A R) ∉ (((Class.cv (nb066AlphaDummy000 A R))).fv) := by
  simpa only [nb066AlphaDummy006] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy000 A R))).fv) 0

theorem nb066_fresh_005 (A : Class) (R : Class) :
    (nb066AlphaDummy008 A R) ∉
      (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy002 A R))).fv) :=
  by
  simpa only [nb066AlphaDummy008] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy002 A R))).fv)
      0

theorem nb066_fresh_006 (A : Class) (R : Class) :
    (nb066AlphaDummy009 A R) ∉
      (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy002 A R))).fv) :=
  by
  simpa only [nb066AlphaDummy009] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy002 A R))).fv)
      1

theorem nb066_distinct_007 (A : Class) (R : Class) :
    (nb066AlphaDummy008 A R) ≠ (nb066AlphaDummy009 A R) := by
  simpa only [nb066AlphaDummy008, nb066AlphaDummy009] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy002 A R))).fv) (i := 0) (j := 1) (by decide))

theorem nb066_fresh_008 (x : Var) (R : Class) :
    (nb066AlphaDummy010 x R) ∉
      (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy004 x R))).fv) :=
  by
  simpa only [nb066AlphaDummy010] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy004 x R))).fv)
      0

theorem nb066_fresh_009 (x : Var) (R : Class) :
    (nb066AlphaDummy011 x R) ∉
      (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy004 x R))).fv) :=
  by
  simpa only [nb066AlphaDummy011] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy004 x R))).fv)
      1

theorem nb066_distinct_010 (x : Var) (R : Class) :
    (nb066AlphaDummy010 x R) ≠ (nb066AlphaDummy011 x R) := by
  simpa only [nb066AlphaDummy010, nb066AlphaDummy011] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy004 x R))).fv) (i := 0) (j := 1) (by decide))

theorem nb066_fresh_011 (A : Class) (R : Class) :
    (nb066AlphaDummy016 A R) ∉ (((Class.cv (nb066AlphaDummy009 A R))).fv) := by
  simpa only [nb066AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy009 A R))).fv) 0

theorem nb066_fresh_012 (A : Class) (R : Class) :
    (nb066AlphaDummy017 A R) ∉ (((Class.cv (nb066AlphaDummy009 A R))).fv) := by
  simpa only [nb066AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy009 A R))).fv) 1

theorem nb066_distinct_013 (A : Class) (R : Class) :
    (nb066AlphaDummy016 A R) ≠ (nb066AlphaDummy017 A R) := by
  simpa only [nb066AlphaDummy016, nb066AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy009 A R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb066_fresh_014 (x : Var) (R : Class) :
    (nb066AlphaDummy018 x R) ∉ (((Class.cv (nb066AlphaDummy011 x R))).fv) := by
  simpa only [nb066AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy011 x R))).fv) 0

theorem nb066_fresh_015 (x : Var) (R : Class) :
    (nb066AlphaDummy019 x R) ∉ (((Class.cv (nb066AlphaDummy011 x R))).fv) := by
  simpa only [nb066AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy011 x R))).fv) 1

theorem nb066_distinct_016 (x : Var) (R : Class) :
    (nb066AlphaDummy018 x R) ≠ (nb066AlphaDummy019 x R) := by
  simpa only [nb066AlphaDummy018, nb066AlphaDummy019] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy011 x R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb066_fresh_017 (A : Class) (R : Class) :
    (nb066AlphaDummy022 A R) ∉
      (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb066AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) 0

theorem nb066_fresh_018 (A : Class) (R : Class) :
    (nb066AlphaDummy023 A R) ∉
      (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb066AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) 1

theorem nb066_fresh_019 (A : Class) (R : Class) :
    (nb066AlphaDummy024 A R) ∉
      (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb066AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) 2

theorem nb066_distinct_020 (A : Class) (R : Class) :
    (nb066AlphaDummy022 A R) ≠ (nb066AlphaDummy023 A R) := by
  simpa only [nb066AlphaDummy022, nb066AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb066_distinct_021 (A : Class) (R : Class) :
    (nb066AlphaDummy022 A R) ≠ (nb066AlphaDummy024 A R) := by
  simpa only [nb066AlphaDummy022, nb066AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb066_distinct_022 (A : Class) (R : Class) :
    (nb066AlphaDummy023 A R) ≠ (nb066AlphaDummy024 A R) := by
  simpa only [nb066AlphaDummy023, nb066AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb066_fresh_023 (x : Var) (R : Class) :
    (nb066AlphaDummy025 x R) ∉
      (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb066AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) 0

theorem nb066_fresh_024 (x : Var) (R : Class) :
    (nb066AlphaDummy026 x R) ∉
      (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb066AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) 1

theorem nb066_fresh_025 (x : Var) (R : Class) :
    (nb066AlphaDummy027 x R) ∉
      (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb066AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) 2

theorem nb066_distinct_026 (x : Var) (R : Class) :
    (nb066AlphaDummy025 x R) ≠ (nb066AlphaDummy026 x R) := by
  simpa only [nb066AlphaDummy025, nb066AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb066_distinct_027 (x : Var) (R : Class) :
    (nb066AlphaDummy025 x R) ≠ (nb066AlphaDummy027 x R) := by
  simpa only [nb066AlphaDummy025, nb066AlphaDummy027] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb066_distinct_028 (x : Var) (R : Class) :
    (nb066AlphaDummy026 x R) ≠ (nb066AlphaDummy027 x R) := by
  simpa only [nb066AlphaDummy026, nb066AlphaDummy027] using
    (freshVar_injective (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb066_fresh_029 (A : Class) (R : Class) :
    (nb066AlphaDummy034 A R) ∉
      (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy023 A R))).fv) :=
  by
  simpa only [nb066AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy023 A R))).fv)
      0

theorem nb066_fresh_030 (A : Class) (R : Class) :
    (nb066AlphaDummy030 A R) ∉
      (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy024 A R))).fv) :=
  by
  simpa only [nb066AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy024 A R))).fv)
      0

theorem nb066_fresh_031 (A : Class) (R : Class) :
    (nb066AlphaDummy036 A R) ∉
      (((Class.cv (nb066AlphaDummy024 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy024 A R))).fv) :=
  by
  simpa only [nb066AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy024 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy024 A R))).fv)
      0

theorem nb066_fresh_032 (x : Var) (R : Class) :
    (nb066AlphaDummy035 x R) ∉
      (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy026 x R))).fv) :=
  by
  simpa only [nb066AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy026 x R))).fv)
      0

theorem nb066_fresh_033 (x : Var) (R : Class) :
    (nb066AlphaDummy031 x R) ∉
      (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy027 x R))).fv) :=
  by
  simpa only [nb066AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy027 x R))).fv)
      0

theorem nb066_fresh_034 (x : Var) (R : Class) :
    (nb066AlphaDummy037 x R) ∉
      (((Class.cv (nb066AlphaDummy027 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy027 x R))).fv) :=
  by
  simpa only [nb066AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb066AlphaDummy027 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy027 x R))).fv)
      0

theorem nb066_fresh_035 (x : Var) : (nb066AlphaDummy007 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb066AlphaDummy007] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb066_fresh_036 (A : Class) (R : Class) :
    (nb066AlphaDummy020 A R) ∉
      (((Wff.classMem (Class.cv (nb066AlphaDummy016 A R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb066AlphaDummy016 A R)) (synC1c))).fv ∪
        ((Class.cv (nb066AlphaDummy016 A R))).fv) :=
  by
  simpa only [nb066AlphaDummy020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb066AlphaDummy016 A R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb066AlphaDummy016 A R)) (synC1c))).fv ∪
        ((Class.cv (nb066AlphaDummy016 A R))).fv)
      0

theorem nb066_fresh_037 (x : Var) (R : Class) :
    (nb066AlphaDummy021 x R) ∉
      (((Wff.classMem (Class.cv (nb066AlphaDummy018 x R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb066AlphaDummy018 x R)) (synC1c))).fv ∪
        ((Class.cv (nb066AlphaDummy018 x R))).fv) :=
  by
  simpa only [nb066AlphaDummy021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb066AlphaDummy018 x R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb066AlphaDummy018 x R)) (synC1c))).fv ∪
        ((Class.cv (nb066AlphaDummy018 x R))).fv)
      0

theorem nb066_fresh_038 (A : Class) (R : Class) :
    (nb066AlphaDummy012 A R) ∉
      (((synCcompl (Class.cab (nb066AlphaDummy008 A R)
              (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
                (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                  (synCphi (Class.cv (nb066AlphaDummy009 A R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb066AlphaDummy008 A R)
              (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
                (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                  (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb066AlphaDummy012] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb066AlphaDummy008 A R)
              (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
                (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                  (synCphi (Class.cv (nb066AlphaDummy009 A R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb066AlphaDummy008 A R)
              (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
                (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                  (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb066_fresh_039 (x : Var) (R : Class) :
    (nb066AlphaDummy013 x R) ∉
      (((synCcompl (Class.cab (nb066AlphaDummy010 x R)
              (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
                (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                  (synCphi (Class.cv (nb066AlphaDummy011 x R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb066AlphaDummy010 x R)
              (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
                (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                  (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb066AlphaDummy013] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb066AlphaDummy010 x R)
              (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
                (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                  (synCphi (Class.cv (nb066AlphaDummy011 x R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb066AlphaDummy010 x R)
              (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
                (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                  (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb066_fresh_040 (A : Class) (R : Class) :
    (nb066AlphaDummy032 A R) ∉
      (((synCcompl (Class.cv (nb066AlphaDummy023 A R)))).fv ∪
        ((synCcompl (Class.cv (nb066AlphaDummy024 A R)))).fv) :=
  by
  simpa only [nb066AlphaDummy032] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb066AlphaDummy023 A R)))).fv ∪
        ((synCcompl (Class.cv (nb066AlphaDummy024 A R)))).fv)
      0

theorem nb066_fresh_041 (x : Var) (R : Class) :
    (nb066AlphaDummy033 x R) ∉
      (((synCcompl (Class.cv (nb066AlphaDummy026 x R)))).fv ∪
        ((synCcompl (Class.cv (nb066AlphaDummy027 x R)))).fv) :=
  by
  simpa only [nb066AlphaDummy033] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb066AlphaDummy026 x R)))).fv ∪
        ((synCcompl (Class.cv (nb066AlphaDummy027 x R)))).fv)
      0

theorem nb066_fresh_042 (A : Class) (R : Class) :
    (nb066AlphaDummy040 A R) ∉
      (((synCcompl (synCphi (Class.cv (nb066AlphaDummy009 A R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb066AlphaDummy040] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb066AlphaDummy009 A R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb066_fresh_043 (x : Var) (R : Class) :
    (nb066AlphaDummy041 x R) ∉
      (((synCcompl (synCphi (Class.cv (nb066AlphaDummy011 x R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb066AlphaDummy041] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb066AlphaDummy011 x R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb066_fresh_044 (A : Class) (R : Class) :
    (nb066AlphaDummy028 A R) ∉
      (((synCnin (Class.cv (nb066AlphaDummy023 A R))
            (Class.cv (nb066AlphaDummy024 A R)))).fv ∪
        ((synCnin (Class.cv (nb066AlphaDummy023 A R))
            (Class.cv (nb066AlphaDummy024 A R)))).fv) :=
  by
  simpa only [nb066AlphaDummy028] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb066AlphaDummy023 A R))
            (Class.cv (nb066AlphaDummy024 A R)))).fv ∪
        ((synCnin (Class.cv (nb066AlphaDummy023 A R))
            (Class.cv (nb066AlphaDummy024 A R)))).fv)
      0

theorem nb066_fresh_045 (x : Var) (R : Class) :
    (nb066AlphaDummy029 x R) ∉
      (((synCnin (Class.cv (nb066AlphaDummy026 x R))
            (Class.cv (nb066AlphaDummy027 x R)))).fv ∪
        ((synCnin (Class.cv (nb066AlphaDummy026 x R))
            (Class.cv (nb066AlphaDummy027 x R)))).fv) :=
  by
  simpa only [nb066AlphaDummy029] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb066AlphaDummy026 x R))
            (Class.cv (nb066AlphaDummy027 x R)))).fv ∪
        ((synCnin (Class.cv (nb066AlphaDummy026 x R))
            (Class.cv (nb066AlphaDummy027 x R)))).fv)
      0

theorem nb066_fresh_046 (A : Class) (R : Class) :
    (nb066AlphaDummy042 A R) ∉
      (((synCphi (Class.cv (nb066AlphaDummy009 A R)))).fv ∪
        ((synCphi (Class.cv (nb066AlphaDummy009 A R)))).fv) :=
  by
  simpa only [nb066AlphaDummy042] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb066AlphaDummy009 A R)))).fv ∪
        ((synCphi (Class.cv (nb066AlphaDummy009 A R)))).fv)
      0

theorem nb066_fresh_047 (x : Var) (R : Class) :
    (nb066AlphaDummy043 x R) ∉
      (((synCphi (Class.cv (nb066AlphaDummy011 x R)))).fv ∪
        ((synCphi (Class.cv (nb066AlphaDummy011 x R)))).fv) :=
  by
  simpa only [nb066AlphaDummy043] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb066AlphaDummy011 x R)))).fv ∪
        ((synCphi (Class.cv (nb066AlphaDummy011 x R)))).fv)
      0

theorem nb066_fresh_048 (A : Class) (R : Class) :
    (nb066AlphaDummy000 A R) ∉ ((A).fv ∪ (R).fv) := by
  simpa only [nb066AlphaDummy000] using freshVar_not_mem ((A).fv ∪ (R).fv) 0

theorem nb066_fresh_049 (A : Class) (R : Class) :
    (nb066AlphaDummy001 A R) ∉ ((A).fv ∪ (R).fv) := by
  simpa only [nb066AlphaDummy001] using freshVar_not_mem ((A).fv ∪ (R).fv) 1

theorem nb066_distinct_050 (A : Class) (R : Class) :
    (nb066AlphaDummy000 A R) ≠ (nb066AlphaDummy001 A R) := by
  simpa only [nb066AlphaDummy000, nb066AlphaDummy001] using
    (freshVar_injective ((A).fv ∪ (R).fv) (i := 0) (j := 1) (by decide))

theorem nb066_fresh_051 (A : Class) (R : Class) :
    (nb066AlphaDummy002 A R) ∉
      ((R).fv ∪ ((synCsn (Class.cv (nb066AlphaDummy000 A R)))).fv) :=
  by
  simpa only [nb066AlphaDummy002] using
    freshVar_not_mem ((R).fv ∪ ((synCsn (Class.cv (nb066AlphaDummy000 A R)))).fv) 0

theorem nb066_fresh_052 (A : Class) (R : Class) :
    (nb066AlphaDummy003 A R) ∉
      ((R).fv ∪ ((synCsn (Class.cv (nb066AlphaDummy000 A R)))).fv) :=
  by
  simpa only [nb066AlphaDummy003] using
    freshVar_not_mem ((R).fv ∪ ((synCsn (Class.cv (nb066AlphaDummy000 A R)))).fv) 1

theorem nb066_distinct_053 (A : Class) (R : Class) :
    (nb066AlphaDummy002 A R) ≠ (nb066AlphaDummy003 A R) := by
  simpa only [nb066AlphaDummy002, nb066AlphaDummy003] using
    (freshVar_injective ((R).fv ∪ ((synCsn (Class.cv (nb066AlphaDummy000 A R)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb066_fresh_054 (x : Var) (R : Class) :
    (nb066AlphaDummy004 x R) ∉ ((R).fv ∪ ((synCsn (Class.cv x))).fv) := by
  simpa only [nb066AlphaDummy004] using
    freshVar_not_mem ((R).fv ∪ ((synCsn (Class.cv x))).fv) 0

theorem nb066_fresh_055 (x : Var) (R : Class) :
    (nb066AlphaDummy005 x R) ∉ ((R).fv ∪ ((synCsn (Class.cv x))).fv) := by
  simpa only [nb066AlphaDummy005] using
    freshVar_not_mem ((R).fv ∪ ((synCsn (Class.cv x))).fv) 1

theorem nb066_distinct_056 (x : Var) (R : Class) :
    (nb066AlphaDummy004 x R) ≠ (nb066AlphaDummy005 x R) := by
  simpa only [nb066AlphaDummy004, nb066AlphaDummy005] using
    (freshVar_injective ((R).fv ∪ ((synCsn (Class.cv x))).fv) (i := 0) (j := 1) (by decide))

theorem nb066_support_mem_0000 (A : Class) (R : Class) :
    (nb066AlphaDummy000 A R) ∈
      ((R).fv ∪ ((synCsn (Class.cv (nb066AlphaDummy000 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0001 (x : Var) (R : Class) :
    x ∈ ((R).fv ∪ ((synCsn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0002 (A : Class) (R : Class) :
    (nb066AlphaDummy000 A R) ∈ (((Class.cv (nb066AlphaDummy000 A R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0003 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0004 (A : Class) (R : Class) :
    (nb066AlphaDummy003 A R) ∈
      (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy002 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0005 (A : Class) (R : Class) :
    (nb066AlphaDummy003 A R) ∈
      (((synCcompl (Class.cab (nb066AlphaDummy008 A R)
              (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
                (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                  (synCphi (Class.cv (nb066AlphaDummy009 A R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb066AlphaDummy008 A R)
              (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
                (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                  (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0006 (x : Var) (R : Class) :
    (nb066AlphaDummy005 x R) ∈
      (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy004 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0007 (x : Var) (R : Class) :
    (nb066AlphaDummy005 x R) ∈
      (((synCcompl (Class.cab (nb066AlphaDummy010 x R)
              (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
                (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                  (synCphi (Class.cv (nb066AlphaDummy011 x R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb066AlphaDummy010 x R)
              (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
                (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                  (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0008 (A : Class) (R : Class) :
    (nb066AlphaDummy003 A R) ∈
      (((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCphi (Class.cv (nb066AlphaDummy009 A R))))))).fv ∪
        ((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCphi (Class.cv (nb066AlphaDummy009 A R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0009 (x : Var) (R : Class) :
    (nb066AlphaDummy005 x R) ∈
      (((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCphi (Class.cv (nb066AlphaDummy011 x R))))))).fv ∪
        ((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCphi (Class.cv (nb066AlphaDummy011 x R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0010 (A : Class) (R : Class) :
    (nb066AlphaDummy009 A R) ∈ (((Class.cv (nb066AlphaDummy009 A R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0011 (x : Var) (R : Class) :
    (nb066AlphaDummy011 x R) ∈ (((Class.cv (nb066AlphaDummy011 x R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0012 (A : Class) (R : Class) :
    (nb066AlphaDummy016 A R) ∈
      (((Wff.classMem (Class.cv (nb066AlphaDummy016 A R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb066AlphaDummy016 A R)) (synC1c))).fv ∪
        ((Class.cv (nb066AlphaDummy016 A R))).fv) :=
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

theorem nb066_support_mem_0013 (x : Var) (R : Class) :
    (nb066AlphaDummy018 x R) ∈
      (((Wff.classMem (Class.cv (nb066AlphaDummy018 x R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb066AlphaDummy018 x R)) (synC1c))).fv ∪
        ((Class.cv (nb066AlphaDummy018 x R))).fv) :=
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

theorem nb066_support_mem_0014 (A : Class) (R : Class) :
    (nb066AlphaDummy016 A R) ∈
      (((Class.cv (nb066AlphaDummy016 A R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0015 (x : Var) (R : Class) :
    (nb066AlphaDummy018 x R) ∈
      (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0016 (A : Class) (R : Class) :
    (nb066AlphaDummy023 A R) ∈
      (((synCnin (Class.cv (nb066AlphaDummy023 A R))
            (Class.cv (nb066AlphaDummy024 A R)))).fv ∪
        ((synCnin (Class.cv (nb066AlphaDummy023 A R))
            (Class.cv (nb066AlphaDummy024 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0017 (x : Var) (R : Class) :
    (nb066AlphaDummy026 x R) ∈
      (((synCnin (Class.cv (nb066AlphaDummy026 x R))
            (Class.cv (nb066AlphaDummy027 x R)))).fv ∪
        ((synCnin (Class.cv (nb066AlphaDummy026 x R))
            (Class.cv (nb066AlphaDummy027 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0018 (A : Class) (R : Class) :
    (nb066AlphaDummy023 A R) ∈
      (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy024 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0019 (x : Var) (R : Class) :
    (nb066AlphaDummy026 x R) ∈
      (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy027 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0020 (A : Class) (R : Class) :
    (nb066AlphaDummy024 A R) ∈
      (((synCnin (Class.cv (nb066AlphaDummy023 A R))
            (Class.cv (nb066AlphaDummy024 A R)))).fv ∪
        ((synCnin (Class.cv (nb066AlphaDummy023 A R))
            (Class.cv (nb066AlphaDummy024 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0021 (x : Var) (R : Class) :
    (nb066AlphaDummy027 x R) ∈
      (((synCnin (Class.cv (nb066AlphaDummy026 x R))
            (Class.cv (nb066AlphaDummy027 x R)))).fv ∪
        ((synCnin (Class.cv (nb066AlphaDummy026 x R))
            (Class.cv (nb066AlphaDummy027 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0022 (A : Class) (R : Class) :
    (nb066AlphaDummy024 A R) ∈
      (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy024 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0023 (x : Var) (R : Class) :
    (nb066AlphaDummy027 x R) ∈
      (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy027 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0024 (A : Class) (R : Class) :
    (nb066AlphaDummy023 A R) ∈
      (((synCcompl (Class.cv (nb066AlphaDummy023 A R)))).fv ∪
        ((synCcompl (Class.cv (nb066AlphaDummy024 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0025 (x : Var) (R : Class) :
    (nb066AlphaDummy026 x R) ∈
      (((synCcompl (Class.cv (nb066AlphaDummy026 x R)))).fv ∪
        ((synCcompl (Class.cv (nb066AlphaDummy027 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0026 (A : Class) (R : Class) :
    (nb066AlphaDummy023 A R) ∈
      (((Class.cv (nb066AlphaDummy023 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy023 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0027 (x : Var) (R : Class) :
    (nb066AlphaDummy026 x R) ∈
      (((Class.cv (nb066AlphaDummy026 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy026 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0028 (A : Class) (R : Class) :
    (nb066AlphaDummy024 A R) ∈
      (((synCcompl (Class.cv (nb066AlphaDummy023 A R)))).fv ∪
        ((synCcompl (Class.cv (nb066AlphaDummy024 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0029 (x : Var) (R : Class) :
    (nb066AlphaDummy027 x R) ∈
      (((synCcompl (Class.cv (nb066AlphaDummy026 x R)))).fv ∪
        ((synCcompl (Class.cv (nb066AlphaDummy027 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0030 (A : Class) (R : Class) :
    (nb066AlphaDummy024 A R) ∈
      (((Class.cv (nb066AlphaDummy024 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy024 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0031 (x : Var) (R : Class) :
    (nb066AlphaDummy027 x R) ∈
      (((Class.cv (nb066AlphaDummy027 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy027 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0032 (A : Class) (R : Class) :
    (nb066AlphaDummy002 A R) ∈
      (((Class.cv (nb066AlphaDummy003 A R))).fv ∪
        ((Class.cv (nb066AlphaDummy002 A R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0033 (A : Class) (R : Class) :
    (nb066AlphaDummy002 A R) ∈
      (((synCcompl (Class.cab (nb066AlphaDummy008 A R)
              (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy003 A R))
                (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                  (synCphi (Class.cv (nb066AlphaDummy009 A R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb066AlphaDummy008 A R)
              (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
                (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                  (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0034 (x : Var) (R : Class) :
    (nb066AlphaDummy004 x R) ∈
      (((Class.cv (nb066AlphaDummy005 x R))).fv ∪
        ((Class.cv (nb066AlphaDummy004 x R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0035 (x : Var) (R : Class) :
    (nb066AlphaDummy004 x R) ∈
      (((synCcompl (Class.cab (nb066AlphaDummy010 x R)
              (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy005 x R))
                (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                  (synCphi (Class.cv (nb066AlphaDummy011 x R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb066AlphaDummy010 x R)
              (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
                (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                  (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0036 (A : Class) (R : Class) :
    (nb066AlphaDummy002 A R) ∈
      (((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb066AlphaDummy008 A R)
            (synWrex (nb066AlphaDummy009 A R) (Class.cv (nb066AlphaDummy002 A R))
              (Wff.classEq (Class.cv (nb066AlphaDummy008 A R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy009 A R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0037 (x : Var) (R : Class) :
    (nb066AlphaDummy004 x R) ∈
      (((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb066AlphaDummy010 x R)
            (synWrex (nb066AlphaDummy011 x R) (Class.cv (nb066AlphaDummy004 x R))
              (Wff.classEq (Class.cv (nb066AlphaDummy010 x R))
                (synCun (synCphi (Class.cv (nb066AlphaDummy011 x R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb066_support_mem_0038 (A : Class) (R : Class) :
    (nb066AlphaDummy009 A R) ∈
      (((synCcompl (synCphi (Class.cv (nb066AlphaDummy009 A R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0039 (x : Var) (R : Class) :
    (nb066AlphaDummy011 x R) ∈
      (((synCcompl (synCphi (Class.cv (nb066AlphaDummy011 x R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0040 (A : Class) (R : Class) :
    (nb066AlphaDummy009 A R) ∈
      (((synCphi (Class.cv (nb066AlphaDummy009 A R)))).fv ∪
        ((synCphi (Class.cv (nb066AlphaDummy009 A R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_support_mem_0041 (x : Var) (R : Class) :
    (nb066AlphaDummy011 x R) ∈
      (((synCphi (Class.cv (nb066AlphaDummy011 x R)))).fv ∪
        ((synCphi (Class.cv (nb066AlphaDummy011 x R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb066_focused_notmem_0000 (A : Class) (R : Class) :
    (nb066AlphaDummy000 A R) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (R).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb066_wpp_notmem_0000 (A : Class) (R : Class) :
    (nb066AlphaDummy000 A R) ∉ (A).fv := by exact (nb066_focused_notmem_0000 A R)

theorem nb066_wpp_notmem_0001 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem nb066_focused_notmem_0001 (A : Class) (R : Class) :
    (nb066AlphaDummy001 A R) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (R).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb066_wpp_notmem_0002 (A : Class) (R : Class) :
    (nb066AlphaDummy001 A R) ∉ (A).fv := by exact (nb066_focused_notmem_0001 A R)

theorem nb066_wpp_notmem_0003 (y : Var) (A : Class) (dv_A_y : y ∉ A.fv) : y ∉ (A).fv := by
  exact dv_A_y

theorem nb066_compact_envfresh_0000 (x : Var) (y : Var) (A : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TEnvFresh [((nb066AlphaDummy000 A R), x), ((nb066AlphaDummy001 A R), y)]
      (A).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb066AlphaDummy000 A R) x (nb066_wpp_notmem_0000 A R)
      (nb066_wpp_notmem_0001 x A dv_A_x)
      (TEnvFresh.consFresh (nb066AlphaDummy001 A R) y (nb066_wpp_notmem_0002 A R)
        (nb066_wpp_notmem_0003 y A dv_A_y) (TEnvFresh.nil (A).fv)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
