/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C059C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_000`. -/
@[expose]
noncomputable def nb059AlphaDummy000 (R : Class) (S_cls : Class) : Var :=
  (freshVar ((S_cls).fv ∪ (R).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_001`. -/
@[expose]
noncomputable def nb059AlphaDummy001 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb059AlphaDummy000 R S_cls)
        (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
          (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_002`. -/
@[expose]
noncomputable def nb059AlphaDummy002 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb059AlphaDummy000 R S_cls)
        (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
          (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_003`. -/
@[expose]
noncomputable def nb059AlphaDummy003 (R : Class) (S_cls : Class) (a : Var) : Var :=
  (freshVar (((Class.cab a (synWa (synWss S_cls (Class.cv a))
          (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_004`. -/
@[expose]
noncomputable def nb059AlphaDummy004 (R : Class) (S_cls : Class) (a : Var) : Var :=
  (freshVar (((Class.cab a (synWa (synWss S_cls (Class.cv a))
          (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_005`. -/
@[expose]
noncomputable def nb059AlphaDummy005 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((synCnin S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
      ((synCnin S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_006`. -/
@[expose]
noncomputable def nb059AlphaDummy006 (S_cls : Class) (a : Var) : Var :=
  (freshVar (((synCnin S_cls (Class.cv a))).fv ∪ ((synCnin S_cls (Class.cv a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_007`. -/
@[expose]
noncomputable def nb059AlphaDummy007 (R : Class) (S_cls : Class) : Var :=
  (freshVar ((S_cls).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_008`. -/
@[expose]
noncomputable def nb059AlphaDummy008 (S_cls : Class) (a : Var) : Var :=
  (freshVar ((S_cls).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_009`. -/
@[expose]
noncomputable def nb059AlphaDummy009 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
          (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
      ((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
          (Class.cv (nb059AlphaDummy000 R S_cls)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_010`. -/
@[expose]
noncomputable def nb059AlphaDummy010 (R : Class) (a : Var) : Var :=
  (freshVar (((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv ∪
      ((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_011`. -/
@[expose]
noncomputable def nb059AlphaDummy011 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
      ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_012`. -/
@[expose]
noncomputable def nb059AlphaDummy012 (R : Class) (a : Var) : Var :=
  (freshVar (((synCima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_013`. -/
@[expose]
noncomputable def nb059AlphaDummy013 (R : Class) (S_cls : Class) : Var :=
  (freshVar ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_014`. -/
@[expose]
noncomputable def nb059AlphaDummy014 (R : Class) (S_cls : Class) : Var :=
  (freshVar ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_015`. -/
@[expose]
noncomputable def nb059AlphaDummy015 (R : Class) (a : Var) : Var :=
  (freshVar ((R).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_016`. -/
@[expose]
noncomputable def nb059AlphaDummy016 (R : Class) (a : Var) : Var :=
  (freshVar ((R).fv ∪ ((Class.cv a)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_017`. -/
@[expose]
noncomputable def nb059AlphaDummy017 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
      ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_018`. -/
@[expose]
noncomputable def nb059AlphaDummy018 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
      ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_019`. -/
@[expose]
noncomputable def nb059AlphaDummy019 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
      ((Class.cv (nb059AlphaDummy015 R a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_020`. -/
@[expose]
noncomputable def nb059AlphaDummy020 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
      ((Class.cv (nb059AlphaDummy015 R a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_021`. -/
@[expose]
noncomputable def nb059AlphaDummy021 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb059AlphaDummy017 R S_cls)
            (synWrex (nb059AlphaDummy018 R S_cls) (Class.cv (nb059AlphaDummy014 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))))))).fv ∪ ((synCcompl
          (Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy013 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_022`. -/
@[expose]
noncomputable def nb059AlphaDummy022 (R : Class) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCphi (Class.cv (nb059AlphaDummy020 R a)))))))).fv ∪ ((synCcompl
          (Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_023`. -/
@[expose]
noncomputable def nb059AlphaDummy023 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb059AlphaDummy017 R S_cls)
          (synWrex (nb059AlphaDummy018 R S_cls) (Class.cv (nb059AlphaDummy014 R S_cls))
            (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
              (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))))).fv ∪
      ((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
            (Class.cv (nb059AlphaDummy014 R S_cls))
            (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
              (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_024`. -/
@[expose]
noncomputable def nb059AlphaDummy024 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cab (nb059AlphaDummy019 R a)
          (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
            (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
              (synCphi (Class.cv (nb059AlphaDummy020 R a))))))).fv ∪
      ((Class.cab (nb059AlphaDummy019 R a)
          (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
            (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
              (synCphi (Class.cv (nb059AlphaDummy020 R a))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_025`. -/
@[expose]
noncomputable def nb059AlphaDummy025 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy018 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_026`. -/
@[expose]
noncomputable def nb059AlphaDummy026 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy018 R S_cls))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_027`. -/
@[expose]
noncomputable def nb059AlphaDummy027 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy020 R a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_028`. -/
@[expose]
noncomputable def nb059AlphaDummy028 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy020 R a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_029`. -/
@[expose]
noncomputable def nb059AlphaDummy029 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb059AlphaDummy025 R S_cls)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb059AlphaDummy025 R S_cls)) (synC1c))).fv ∪
      ((Class.cv (nb059AlphaDummy025 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_030`. -/
@[expose]
noncomputable def nb059AlphaDummy030 (R : Class) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb059AlphaDummy027 R a)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb059AlphaDummy027 R a)) (synC1c))).fv ∪
      ((Class.cv (nb059AlphaDummy027 R a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_031`. -/
@[expose]
noncomputable def nb059AlphaDummy031 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_032`. -/
@[expose]
noncomputable def nb059AlphaDummy032 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_033`. -/
@[expose]
noncomputable def nb059AlphaDummy033 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_034`. -/
@[expose]
noncomputable def nb059AlphaDummy034 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_035`. -/
@[expose]
noncomputable def nb059AlphaDummy035 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_036`. -/
@[expose]
noncomputable def nb059AlphaDummy036 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_037`. -/
@[expose]
noncomputable def nb059AlphaDummy037 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
          (Class.cv (nb059AlphaDummy033 R S_cls)))).fv ∪
      ((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
          (Class.cv (nb059AlphaDummy033 R S_cls)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_038`. -/
@[expose]
noncomputable def nb059AlphaDummy038 (R : Class) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb059AlphaDummy035 R a))
          (Class.cv (nb059AlphaDummy036 R a)))).fv ∪
      ((synCnin (Class.cv (nb059AlphaDummy035 R a))
          (Class.cv (nb059AlphaDummy036 R a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_039`. -/
@[expose]
noncomputable def nb059AlphaDummy039 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy032 R S_cls))).fv ∪
      ((Class.cv (nb059AlphaDummy033 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_040`. -/
@[expose]
noncomputable def nb059AlphaDummy040 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy035 R a))).fv ∪
      ((Class.cv (nb059AlphaDummy036 R a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_041`. -/
@[expose]
noncomputable def nb059AlphaDummy041 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb059AlphaDummy032 R S_cls)))).fv ∪
      ((synCcompl (Class.cv (nb059AlphaDummy033 R S_cls)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_042`. -/
@[expose]
noncomputable def nb059AlphaDummy042 (R : Class) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb059AlphaDummy035 R a)))).fv ∪
      ((synCcompl (Class.cv (nb059AlphaDummy036 R a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_043`. -/
@[expose]
noncomputable def nb059AlphaDummy043 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy032 R S_cls))).fv ∪
      ((Class.cv (nb059AlphaDummy032 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_044`. -/
@[expose]
noncomputable def nb059AlphaDummy044 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy035 R a))).fv ∪
      ((Class.cv (nb059AlphaDummy035 R a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_045`. -/
@[expose]
noncomputable def nb059AlphaDummy045 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy033 R S_cls))).fv ∪
      ((Class.cv (nb059AlphaDummy033 R S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_046`. -/
@[expose]
noncomputable def nb059AlphaDummy046 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059AlphaDummy036 R a))).fv ∪
      ((Class.cv (nb059AlphaDummy036 R a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_047`. -/
@[expose]
noncomputable def nb059AlphaDummy047 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb059AlphaDummy017 R S_cls)
          (synWrex (nb059AlphaDummy018 R S_cls) (Class.cv (nb059AlphaDummy013 R S_cls))
            (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
              (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb059AlphaDummy017 R S_cls)
          (synWrex (nb059AlphaDummy018 R S_cls) (Class.cv (nb059AlphaDummy013 R S_cls))
            (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
              (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_048`. -/
@[expose]
noncomputable def nb059AlphaDummy048 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cab (nb059AlphaDummy019 R a)
          (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
            (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
              (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb059AlphaDummy019 R a)
          (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
            (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
              (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_049`. -/
@[expose]
noncomputable def nb059AlphaDummy049 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_050`. -/
@[expose]
noncomputable def nb059AlphaDummy050 (R : Class) (a : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb059AlphaDummy020 R a))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_051`. -/
@[expose]
noncomputable def nb059AlphaDummy051 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))).fv ∪
      ((synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb059_alpha_dummy_052`. -/
@[expose]
noncomputable def nb059AlphaDummy052 (R : Class) (a : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb059AlphaDummy020 R a)))).fv ∪
      ((synCphi (Class.cv (nb059AlphaDummy020 R a)))).fv) 0)

theorem nb059_fresh_000 (R : Class) (S_cls : Class) (a : Var) :
    (nb059AlphaDummy003 R S_cls a) ∉
      (((Class.cab a (synWa (synWss S_cls (Class.cv a))
            (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv) :=
  by
  simpa only [nb059AlphaDummy003] using
    freshVar_not_mem
      (((Class.cab a (synWa (synWss S_cls (Class.cv a))
            (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv)
      0

theorem nb059_fresh_001 (R : Class) (S_cls : Class) (a : Var) :
    (nb059AlphaDummy004 R S_cls a) ∉
      (((Class.cab a (synWa (synWss S_cls (Class.cv a))
            (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv) :=
  by
  simpa only [nb059AlphaDummy004] using
    freshVar_not_mem
      (((Class.cab a (synWa (synWss S_cls (Class.cv a))
            (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv)
      1

theorem nb059_distinct_002 (R : Class) (S_cls : Class) (a : Var) :
    (nb059AlphaDummy003 R S_cls a) ≠ (nb059AlphaDummy004 R S_cls a) := by
  simpa only [nb059AlphaDummy003, nb059AlphaDummy004] using
    (freshVar_injective (((Class.cab a (synWa (synWss S_cls (Class.cv a))
            (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb059_fresh_003 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy001 R S_cls) ∉
      (((Class.cab (nb059AlphaDummy000 R S_cls)
          (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
            (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
              (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv) :=
  by
  simpa only [nb059AlphaDummy001] using
    freshVar_not_mem
      (((Class.cab (nb059AlphaDummy000 R S_cls)
          (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
            (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
              (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv)
      0

theorem nb059_fresh_004 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy002 R S_cls) ∉
      (((Class.cab (nb059AlphaDummy000 R S_cls)
          (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
            (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
              (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv) :=
  by
  simpa only [nb059AlphaDummy002] using
    freshVar_not_mem
      (((Class.cab (nb059AlphaDummy000 R S_cls)
          (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
            (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
              (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv)
      1

theorem nb059_distinct_005 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy001 R S_cls) ≠ (nb059AlphaDummy002 R S_cls) := by
  simpa only [nb059AlphaDummy001, nb059AlphaDummy002] using
    (freshVar_injective (((Class.cab (nb059AlphaDummy000 R S_cls)
          (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
            (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
              (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb059_fresh_006 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy047 R S_cls) ∉
      (((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy013 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb059AlphaDummy017 R S_cls)
            (synWrex (nb059AlphaDummy018 R S_cls) (Class.cv (nb059AlphaDummy013 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb059AlphaDummy047] using
    freshVar_not_mem
      (((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy013 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb059AlphaDummy017 R S_cls)
            (synWrex (nb059AlphaDummy018 R S_cls) (Class.cv (nb059AlphaDummy013 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb059_fresh_007 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy023 R S_cls) ∉
      (((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy014 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))))).fv ∪
        ((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy014 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))))).fv) :=
  by
  simpa only [nb059AlphaDummy023] using
    freshVar_not_mem
      (((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy014 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))))).fv ∪
        ((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy014 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))))).fv)
      0

theorem nb059_fresh_008 (R : Class) (a : Var) :
    (nb059AlphaDummy048 R a) ∉
      (((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb059AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb059_fresh_009 (R : Class) (a : Var) :
    (nb059AlphaDummy024 R a) ∉
      (((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCphi (Class.cv (nb059AlphaDummy020 R a))))))).fv ∪
        ((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCphi (Class.cv (nb059AlphaDummy020 R a))))))).fv) :=
  by
  simpa only [nb059AlphaDummy024] using
    freshVar_not_mem
      (((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCphi (Class.cv (nb059AlphaDummy020 R a))))))).fv ∪
        ((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCphi (Class.cv (nb059AlphaDummy020 R a))))))).fv)
      0

theorem nb059_fresh_010 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy017 R S_cls) ∉
      (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy017] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy013 R S_cls))).fv)
      0

theorem nb059_fresh_011 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy018 R S_cls) ∉
      (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy018] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy013 R S_cls))).fv)
      1

theorem nb059_distinct_012 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy017 R S_cls) ≠ (nb059AlphaDummy018 R S_cls) := by
  simpa only [nb059AlphaDummy017, nb059AlphaDummy018] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) (i := 0) (j := 1) (by decide))

theorem nb059_fresh_013 (R : Class) (a : Var) :
    (nb059AlphaDummy019 R a) ∉
      (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy015 R a))).fv) :=
  by
  simpa only [nb059AlphaDummy019] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy015 R a))).fv)
      0

theorem nb059_fresh_014 (R : Class) (a : Var) :
    (nb059AlphaDummy020 R a) ∉
      (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy015 R a))).fv) :=
  by
  simpa only [nb059AlphaDummy020] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy015 R a))).fv)
      1

theorem nb059_distinct_015 (R : Class) (a : Var) :
    (nb059AlphaDummy019 R a) ≠ (nb059AlphaDummy020 R a) := by
  simpa only [nb059AlphaDummy019, nb059AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy015 R a))).fv) (i := 0) (j := 1) (by decide))

theorem nb059_fresh_016 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy025 R S_cls) ∉ (((Class.cv (nb059AlphaDummy018 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy018 R S_cls))).fv) 0

theorem nb059_fresh_017 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy026 R S_cls) ∉ (((Class.cv (nb059AlphaDummy018 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy018 R S_cls))).fv) 1

theorem nb059_distinct_018 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy025 R S_cls) ≠ (nb059AlphaDummy026 R S_cls) := by
  simpa only [nb059AlphaDummy025, nb059AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy018 R S_cls))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb059_fresh_019 (R : Class) (a : Var) :
    (nb059AlphaDummy027 R a) ∉ (((Class.cv (nb059AlphaDummy020 R a))).fv) := by
  simpa only [nb059AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy020 R a))).fv) 0

theorem nb059_fresh_020 (R : Class) (a : Var) :
    (nb059AlphaDummy028 R a) ∉ (((Class.cv (nb059AlphaDummy020 R a))).fv) := by
  simpa only [nb059AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy020 R a))).fv) 1

theorem nb059_distinct_021 (R : Class) (a : Var) :
    (nb059AlphaDummy027 R a) ≠ (nb059AlphaDummy028 R a) := by
  simpa only [nb059AlphaDummy027, nb059AlphaDummy028] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy020 R a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb059_fresh_022 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy031 R S_cls) ∉
      (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb059AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) 0

theorem nb059_fresh_023 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy032 R S_cls) ∉
      (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb059AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) 1

theorem nb059_fresh_024 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy033 R S_cls) ∉
      (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb059AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) 2

theorem nb059_distinct_025 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy031 R S_cls) ≠ (nb059AlphaDummy032 R S_cls) := by
  simpa only [nb059AlphaDummy031, nb059AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb059_distinct_026 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy031 R S_cls) ≠ (nb059AlphaDummy033 R S_cls) := by
  simpa only [nb059AlphaDummy031, nb059AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb059_distinct_027 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy032 R S_cls) ≠ (nb059AlphaDummy033 R S_cls) := by
  simpa only [nb059AlphaDummy032, nb059AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb059_fresh_028 (R : Class) (a : Var) :
    (nb059AlphaDummy034 R a) ∉
      (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb059AlphaDummy034] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) 0

theorem nb059_fresh_029 (R : Class) (a : Var) :
    (nb059AlphaDummy035 R a) ∉
      (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb059AlphaDummy035] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) 1

theorem nb059_fresh_030 (R : Class) (a : Var) :
    (nb059AlphaDummy036 R a) ∉
      (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb059AlphaDummy036] using
    freshVar_not_mem (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) 2

theorem nb059_distinct_031 (R : Class) (a : Var) :
    (nb059AlphaDummy034 R a) ≠ (nb059AlphaDummy035 R a) := by
  simpa only [nb059AlphaDummy034, nb059AlphaDummy035] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb059_distinct_032 (R : Class) (a : Var) :
    (nb059AlphaDummy034 R a) ≠ (nb059AlphaDummy036 R a) := by
  simpa only [nb059AlphaDummy034, nb059AlphaDummy036] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb059_distinct_033 (R : Class) (a : Var) :
    (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy036 R a) := by
  simpa only [nb059AlphaDummy035, nb059AlphaDummy036] using
    (freshVar_injective (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb059_fresh_034 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy043 R S_cls) ∉
      (((Class.cv (nb059AlphaDummy032 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy032 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy032 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy032 R S_cls))).fv)
      0

theorem nb059_fresh_035 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy039 R S_cls) ∉
      (((Class.cv (nb059AlphaDummy032 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy033 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy039] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy032 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy033 R S_cls))).fv)
      0

theorem nb059_fresh_036 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy045 R S_cls) ∉
      (((Class.cv (nb059AlphaDummy033 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy033 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy033 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy033 R S_cls))).fv)
      0

theorem nb059_fresh_037 (R : Class) (a : Var) :
    (nb059AlphaDummy044 R a) ∉
      (((Class.cv (nb059AlphaDummy035 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy035 R a))).fv) :=
  by
  simpa only [nb059AlphaDummy044] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy035 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy035 R a))).fv)
      0

theorem nb059_fresh_038 (R : Class) (a : Var) :
    (nb059AlphaDummy040 R a) ∉
      (((Class.cv (nb059AlphaDummy035 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy036 R a))).fv) :=
  by
  simpa only [nb059AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy035 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy036 R a))).fv)
      0

theorem nb059_fresh_039 (R : Class) (a : Var) :
    (nb059AlphaDummy046 R a) ∉
      (((Class.cv (nb059AlphaDummy036 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy036 R a))).fv) :=
  by
  simpa only [nb059AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb059AlphaDummy036 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy036 R a))).fv)
      0

theorem nb059_fresh_040 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy029 R S_cls) ∉
      (((Wff.classMem (Class.cv (nb059AlphaDummy025 R S_cls)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb059AlphaDummy025 R S_cls)) (synC1c))).fv ∪
        ((Class.cv (nb059AlphaDummy025 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy029] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb059AlphaDummy025 R S_cls)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb059AlphaDummy025 R S_cls)) (synC1c))).fv ∪
        ((Class.cv (nb059AlphaDummy025 R S_cls))).fv)
      0

theorem nb059_fresh_041 (R : Class) (a : Var) :
    (nb059AlphaDummy030 R a) ∉
      (((Wff.classMem (Class.cv (nb059AlphaDummy027 R a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb059AlphaDummy027 R a)) (synC1c))).fv ∪
        ((Class.cv (nb059AlphaDummy027 R a))).fv) :=
  by
  simpa only [nb059AlphaDummy030] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb059AlphaDummy027 R a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb059AlphaDummy027 R a)) (synC1c))).fv ∪
        ((Class.cv (nb059AlphaDummy027 R a))).fv)
      0

theorem nb059_fresh_042 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy021 R S_cls) ∉
      (((synCcompl (Class.cab (nb059AlphaDummy017 R S_cls)
              (synWrex (nb059AlphaDummy018 R S_cls)
                (Class.cv (nb059AlphaDummy014 R S_cls))
                (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                  (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))))))).fv ∪ ((synCcompl
            (Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
                (Class.cv (nb059AlphaDummy013 R S_cls))
                (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                  (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb059AlphaDummy021] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb059AlphaDummy017 R S_cls)
              (synWrex (nb059AlphaDummy018 R S_cls)
                (Class.cv (nb059AlphaDummy014 R S_cls))
                (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                  (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))))))).fv ∪ ((synCcompl
            (Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
                (Class.cv (nb059AlphaDummy013 R S_cls))
                (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                  (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb059_fresh_043 (R : Class) (a : Var) :
    (nb059AlphaDummy022 R a) ∉
      (((synCcompl (Class.cab (nb059AlphaDummy019 R a)
              (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
                (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                  (synCphi (Class.cv (nb059AlphaDummy020 R a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb059AlphaDummy019 R a)
              (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
                (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                  (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb059AlphaDummy022] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb059AlphaDummy019 R a)
              (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
                (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                  (synCphi (Class.cv (nb059AlphaDummy020 R a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb059AlphaDummy019 R a)
              (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
                (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                  (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb059_fresh_044 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy041 R S_cls) ∉
      (((synCcompl (Class.cv (nb059AlphaDummy032 R S_cls)))).fv ∪
        ((synCcompl (Class.cv (nb059AlphaDummy033 R S_cls)))).fv) :=
  by
  simpa only [nb059AlphaDummy041] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb059AlphaDummy032 R S_cls)))).fv ∪
        ((synCcompl (Class.cv (nb059AlphaDummy033 R S_cls)))).fv)
      0

theorem nb059_fresh_045 (R : Class) (a : Var) :
    (nb059AlphaDummy042 R a) ∉
      (((synCcompl (Class.cv (nb059AlphaDummy035 R a)))).fv ∪
        ((synCcompl (Class.cv (nb059AlphaDummy036 R a)))).fv) :=
  by
  simpa only [nb059AlphaDummy042] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb059AlphaDummy035 R a)))).fv ∪
        ((synCcompl (Class.cv (nb059AlphaDummy036 R a)))).fv)
      0

theorem nb059_fresh_046 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy049 R S_cls) ∉
      (((synCcompl (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb059AlphaDummy049] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb059_fresh_047 (R : Class) (a : Var) :
    (nb059AlphaDummy050 R a) ∉
      (((synCcompl (synCphi (Class.cv (nb059AlphaDummy020 R a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb059AlphaDummy050] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb059AlphaDummy020 R a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb059_fresh_048 (R : Class) (a : Var) :
    (nb059AlphaDummy012 R a) ∉ (((synCima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) :=
  by
  simpa only [nb059AlphaDummy012] using
    freshVar_not_mem (((synCima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) 0

theorem nb059_fresh_049 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy011 R S_cls) ∉
      (((synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy011] using
    freshVar_not_mem
      (((synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((Class.cv (nb059AlphaDummy000 R S_cls))).fv)
      0

theorem nb059_fresh_050 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy037 R S_cls) ∉
      (((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls)))).fv ∪
        ((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls)))).fv) :=
  by
  simpa only [nb059AlphaDummy037] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls)))).fv ∪
        ((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls)))).fv)
      0

theorem nb059_fresh_051 (R : Class) (a : Var) :
    (nb059AlphaDummy038 R a) ∉
      (((synCnin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a)))).fv ∪
        ((synCnin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a)))).fv) :=
  by
  simpa only [nb059AlphaDummy038] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a)))).fv ∪
        ((synCnin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a)))).fv)
      0

theorem nb059_fresh_052 (R : Class) (a : Var) :
    (nb059AlphaDummy010 R a) ∉
      (((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv ∪
        ((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv) :=
  by
  simpa only [nb059AlphaDummy010] using
    freshVar_not_mem
      (((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv ∪
        ((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv)
      0

theorem nb059_fresh_053 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy009 R S_cls) ∉
      (((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))).fv) :=
  by
  simpa only [nb059AlphaDummy009] using
    freshVar_not_mem
      (((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))).fv)
      0

theorem nb059_fresh_054 (S_cls : Class) (a : Var) :
    (nb059AlphaDummy006 S_cls a) ∉
      (((synCnin S_cls (Class.cv a))).fv ∪ ((synCnin S_cls (Class.cv a))).fv) :=
  by
  simpa only [nb059AlphaDummy006] using
    freshVar_not_mem
      (((synCnin S_cls (Class.cv a))).fv ∪ ((synCnin S_cls (Class.cv a))).fv) 0

theorem nb059_fresh_055 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy005 R S_cls) ∉
      (((synCnin S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((synCnin S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))).fv) :=
  by
  simpa only [nb059AlphaDummy005] using
    freshVar_not_mem
      (((synCnin S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((synCnin S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))).fv)
      0

theorem nb059_fresh_056 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy051 R S_cls) ∉
      (((synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))).fv ∪
        ((synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))).fv) :=
  by
  simpa only [nb059AlphaDummy051] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))).fv ∪
        ((synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))).fv)
      0

theorem nb059_fresh_057 (R : Class) (a : Var) :
    (nb059AlphaDummy052 R a) ∉
      (((synCphi (Class.cv (nb059AlphaDummy020 R a)))).fv ∪
        ((synCphi (Class.cv (nb059AlphaDummy020 R a)))).fv) :=
  by
  simpa only [nb059AlphaDummy052] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb059AlphaDummy020 R a)))).fv ∪
        ((synCphi (Class.cv (nb059AlphaDummy020 R a)))).fv)
      0

theorem nb059_fresh_058 (R : Class) (a : Var) :
    (nb059AlphaDummy015 R a) ∉ ((R).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb059AlphaDummy015] using freshVar_not_mem ((R).fv ∪ ((Class.cv a)).fv) 0

theorem nb059_fresh_059 (R : Class) (a : Var) :
    (nb059AlphaDummy016 R a) ∉ ((R).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb059AlphaDummy016] using freshVar_not_mem ((R).fv ∪ ((Class.cv a)).fv) 1

theorem nb059_distinct_060 (R : Class) (a : Var) :
    (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy016 R a) := by
  simpa only [nb059AlphaDummy015, nb059AlphaDummy016] using
    (freshVar_injective ((R).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb059_fresh_061 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy013 R S_cls) ∉
      ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy013] using
    freshVar_not_mem ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 0

theorem nb059_fresh_062 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy014 R S_cls) ∉
      ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy014] using
    freshVar_not_mem ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 1

theorem nb059_distinct_063 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy013 R S_cls) ≠ (nb059AlphaDummy014 R S_cls) := by
  simpa only [nb059AlphaDummy013, nb059AlphaDummy014] using
    (freshVar_injective ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb059_fresh_064 (S_cls : Class) (a : Var) :
    (nb059AlphaDummy008 S_cls a) ∉ ((S_cls).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb059AlphaDummy008] using
    freshVar_not_mem ((S_cls).fv ∪ ((Class.cv a)).fv) 0

theorem nb059_fresh_065 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy007 R S_cls) ∉
      ((S_cls).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) :=
  by
  simpa only [nb059AlphaDummy007] using
    freshVar_not_mem ((S_cls).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 0

theorem nb059_fresh_066 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy000 R S_cls) ∉ ((S_cls).fv ∪ (R).fv) := by
  simpa only [nb059AlphaDummy000] using freshVar_not_mem ((S_cls).fv ∪ (R).fv) 0

theorem nb059_support_mem_0000 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy000 R S_cls) ∈
      (((synCnin S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((synCnin S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0001 (S_cls : Class) (a : Var) :
    a ∈ (((synCnin S_cls (Class.cv a))).fv ∪ ((synCnin S_cls (Class.cv a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0002 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy000 R S_cls) ∈
      ((S_cls).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0003 (S_cls : Class) (a : Var) :
    a ∈ ((S_cls).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0004 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy000 R S_cls) ∈
      (((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0005 (R : Class) (a : Var) :
    a ∈
      (((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv ∪
        ((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0006 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy000 R S_cls) ∈
      (((synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
        ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0007 (R : Class) (a : Var) :
    a ∈ (((synCima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0008 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy000 R S_cls) ∈
      ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0009 (R : Class) (a : Var) : a ∈ ((R).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0010 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy014 R S_cls) ∈
      (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0011 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy014 R S_cls) ∈
      (((synCcompl (Class.cab (nb059AlphaDummy017 R S_cls)
              (synWrex (nb059AlphaDummy018 R S_cls)
                (Class.cv (nb059AlphaDummy014 R S_cls))
                (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                  (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))))))).fv ∪ ((synCcompl
            (Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
                (Class.cv (nb059AlphaDummy013 R S_cls))
                (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                  (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0012 (R : Class) (a : Var) :
    (nb059AlphaDummy016 R a) ∈
      (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy015 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0013 (R : Class) (a : Var) :
    (nb059AlphaDummy016 R a) ∈
      (((synCcompl (Class.cab (nb059AlphaDummy019 R a)
              (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
                (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                  (synCphi (Class.cv (nb059AlphaDummy020 R a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb059AlphaDummy019 R a)
              (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
                (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                  (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0014 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy014 R S_cls) ∈
      (((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy014 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))))).fv ∪
        ((Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy014 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0015 (R : Class) (a : Var) :
    (nb059AlphaDummy016 R a) ∈
      (((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCphi (Class.cv (nb059AlphaDummy020 R a))))))).fv ∪
        ((Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy016 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCphi (Class.cv (nb059AlphaDummy020 R a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0016 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy018 R S_cls) ∈ (((Class.cv (nb059AlphaDummy018 R S_cls))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0017 (R : Class) (a : Var) :
    (nb059AlphaDummy020 R a) ∈ (((Class.cv (nb059AlphaDummy020 R a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0018 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy025 R S_cls) ∈
      (((Wff.classMem (Class.cv (nb059AlphaDummy025 R S_cls)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb059AlphaDummy025 R S_cls)) (synC1c))).fv ∪
        ((Class.cv (nb059AlphaDummy025 R S_cls))).fv) :=
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

theorem nb059_support_mem_0019 (R : Class) (a : Var) :
    (nb059AlphaDummy027 R a) ∈
      (((Wff.classMem (Class.cv (nb059AlphaDummy027 R a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb059AlphaDummy027 R a)) (synC1c))).fv ∪
        ((Class.cv (nb059AlphaDummy027 R a))).fv) :=
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

theorem nb059_support_mem_0020 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy025 R S_cls) ∈
      (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0021 (R : Class) (a : Var) :
    (nb059AlphaDummy027 R a) ∈
      (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0022 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy032 R S_cls) ∈
      (((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls)))).fv ∪
        ((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0023 (R : Class) (a : Var) :
    (nb059AlphaDummy035 R a) ∈
      (((synCnin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a)))).fv ∪
        ((synCnin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0024 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy032 R S_cls) ∈
      (((Class.cv (nb059AlphaDummy032 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy033 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0025 (R : Class) (a : Var) :
    (nb059AlphaDummy035 R a) ∈
      (((Class.cv (nb059AlphaDummy035 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy036 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0026 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy033 R S_cls) ∈
      (((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls)))).fv ∪
        ((synCnin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0027 (R : Class) (a : Var) :
    (nb059AlphaDummy036 R a) ∈
      (((synCnin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a)))).fv ∪
        ((synCnin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0028 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy033 R S_cls) ∈
      (((Class.cv (nb059AlphaDummy032 R S_cls))).fv ∪
        ((Class.cv (nb059AlphaDummy033 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0029 (R : Class) (a : Var) :
    (nb059AlphaDummy036 R a) ∈
      (((Class.cv (nb059AlphaDummy035 R a))).fv ∪
        ((Class.cv (nb059AlphaDummy036 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
