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

/-! Certificates from `AlphaSupport.NAR4H5C097M3Part001Stage1`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_000`. -/
@[expose]
noncomputable def nb097AlphaDummy000 (C : Class) (F : Class) : Var :=
  (freshVar ((F).fv ∪ (C).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_001`. -/
@[expose]
noncomputable def nb097AlphaDummy001 (C : Class) (F : Class) : Var :=
  (freshVar ((F).fv ∪ (C).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_002`. -/
@[expose]
noncomputable def nb097AlphaDummy002 (C : Class) (F : Class) : Var :=
  (freshVar (({(nb097AlphaDummy001 C F)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_003`. -/
@[expose]
noncomputable def nb097AlphaDummy003 (C : Class) (k : Var) (m : Var) (F : Class) :
    Var :=
  (freshVar (({ m } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_004`. -/
@[expose]
noncomputable def nb097AlphaDummy004 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
          (Class.cab (nb097AlphaDummy001 C F) (synWa
              (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
              (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                  (Class.cv (nb097AlphaDummy000 C F))))))
          (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_005`. -/
@[expose]
noncomputable def nb097AlphaDummy005 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
          (Class.cab (nb097AlphaDummy001 C F) (synWa
              (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
              (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                  (Class.cv (nb097AlphaDummy000 C F))))))
          (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_006`. -/
@[expose]
noncomputable def nb097AlphaDummy006 (C : Class) (k : Var) (m : Var) (F : Class) :
    Var :=
  (freshVar (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
            (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
              (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
          (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_007`. -/
@[expose]
noncomputable def nb097AlphaDummy007 (C : Class) (k : Var) (m : Var) (F : Class) :
    Var :=
  (freshVar (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
            (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
              (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
          (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_008`. -/
@[expose]
noncomputable def nb097AlphaDummy008 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
      ((Class.cv (nb097AlphaDummy000 C F))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_009`. -/
@[expose]
noncomputable def nb097AlphaDummy009 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
      ((Class.cv (nb097AlphaDummy000 C F))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_010`. -/
@[expose]
noncomputable def nb097AlphaDummy010 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_011`. -/
@[expose]
noncomputable def nb097AlphaDummy011 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_012`. -/
@[expose]
noncomputable def nb097AlphaDummy012 (C : Class) (F : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCphi (Class.cv (nb097AlphaDummy009 C F)))))))).fv ∪ ((synCcompl
          (Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_013`. -/
@[expose]
noncomputable def nb097AlphaDummy013 (k : Var) (m : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCphi (Class.cv (nb097AlphaDummy011 k m)))))))).fv ∪ ((synCcompl
          (Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_014`. -/
@[expose]
noncomputable def nb097AlphaDummy014 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cab (nb097AlphaDummy008 C F)
          (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
            (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
              (synCphi (Class.cv (nb097AlphaDummy009 C F))))))).fv ∪
      ((Class.cab (nb097AlphaDummy008 C F)
          (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
            (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
              (synCphi (Class.cv (nb097AlphaDummy009 C F))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_015`. -/
@[expose]
noncomputable def nb097AlphaDummy015 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cab (nb097AlphaDummy010 k m)
          (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
            (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
              (synCphi (Class.cv (nb097AlphaDummy011 k m))))))).fv ∪
      ((Class.cab (nb097AlphaDummy010 k m) (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
            (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
              (synCphi (Class.cv (nb097AlphaDummy011 k m))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_016`. -/
@[expose]
noncomputable def nb097AlphaDummy016 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy009 C F))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_017`. -/
@[expose]
noncomputable def nb097AlphaDummy017 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy009 C F))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_018`. -/
@[expose]
noncomputable def nb097AlphaDummy018 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy011 k m))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_019`. -/
@[expose]
noncomputable def nb097AlphaDummy019 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy011 k m))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_020`. -/
@[expose]
noncomputable def nb097AlphaDummy020 (C : Class) (F : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb097AlphaDummy016 C F)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb097AlphaDummy016 C F)) (synC1c))).fv ∪
      ((Class.cv (nb097AlphaDummy016 C F))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_021`. -/
@[expose]
noncomputable def nb097AlphaDummy021 (k : Var) (m : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb097AlphaDummy018 k m)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb097AlphaDummy018 k m)) (synC1c))).fv ∪
      ((Class.cv (nb097AlphaDummy018 k m))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_022`. -/
@[expose]
noncomputable def nb097AlphaDummy022 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_023`. -/
@[expose]
noncomputable def nb097AlphaDummy023 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_024`. -/
@[expose]
noncomputable def nb097AlphaDummy024 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_025`. -/
@[expose]
noncomputable def nb097AlphaDummy025 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_026`. -/
@[expose]
noncomputable def nb097AlphaDummy026 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_027`. -/
@[expose]
noncomputable def nb097AlphaDummy027 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_028`. -/
@[expose]
noncomputable def nb097AlphaDummy028 (C : Class) (F : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb097AlphaDummy023 C F))
          (Class.cv (nb097AlphaDummy024 C F)))).fv ∪
      ((synCnin (Class.cv (nb097AlphaDummy023 C F))
          (Class.cv (nb097AlphaDummy024 C F)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_029`. -/
@[expose]
noncomputable def nb097AlphaDummy029 (k : Var) (m : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb097AlphaDummy026 k m))
          (Class.cv (nb097AlphaDummy027 k m)))).fv ∪
      ((synCnin (Class.cv (nb097AlphaDummy026 k m))
          (Class.cv (nb097AlphaDummy027 k m)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_030`. -/
@[expose]
noncomputable def nb097AlphaDummy030 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
      ((Class.cv (nb097AlphaDummy024 C F))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_031`. -/
@[expose]
noncomputable def nb097AlphaDummy031 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
      ((Class.cv (nb097AlphaDummy027 k m))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_032`. -/
@[expose]
noncomputable def nb097AlphaDummy032 (C : Class) (F : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb097AlphaDummy023 C F)))).fv ∪
      ((synCcompl (Class.cv (nb097AlphaDummy024 C F)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_033`. -/
@[expose]
noncomputable def nb097AlphaDummy033 (k : Var) (m : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb097AlphaDummy026 k m)))).fv ∪
      ((synCcompl (Class.cv (nb097AlphaDummy027 k m)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_034`. -/
@[expose]
noncomputable def nb097AlphaDummy034 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
      ((Class.cv (nb097AlphaDummy023 C F))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_035`. -/
@[expose]
noncomputable def nb097AlphaDummy035 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
      ((Class.cv (nb097AlphaDummy026 k m))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_036`. -/
@[expose]
noncomputable def nb097AlphaDummy036 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy024 C F))).fv ∪
      ((Class.cv (nb097AlphaDummy024 C F))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_037`. -/
@[expose]
noncomputable def nb097AlphaDummy037 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy027 k m))).fv ∪
      ((Class.cv (nb097AlphaDummy027 k m))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_038`. -/
@[expose]
noncomputable def nb097AlphaDummy038 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cab (nb097AlphaDummy008 C F)
          (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
            (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
              (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb097AlphaDummy008 C F)
          (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
            (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
              (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_039`. -/
@[expose]
noncomputable def nb097AlphaDummy039 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cab (nb097AlphaDummy010 k m)
          (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
            (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
              (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb097AlphaDummy010 k m)
          (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
            (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
              (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_040`. -/
@[expose]
noncomputable def nb097AlphaDummy040 (C : Class) (F : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb097AlphaDummy009 C F))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_041`. -/
@[expose]
noncomputable def nb097AlphaDummy041 (k : Var) (m : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb097AlphaDummy011 k m))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_042`. -/
@[expose]
noncomputable def nb097AlphaDummy042 (C : Class) (F : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb097AlphaDummy009 C F)))).fv ∪
      ((synCphi (Class.cv (nb097AlphaDummy009 C F)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_043`. -/
@[expose]
noncomputable def nb097AlphaDummy043 (k : Var) (m : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb097AlphaDummy011 k m)))).fv ∪
      ((synCphi (Class.cv (nb097AlphaDummy011 k m)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_044`. -/
@[expose]
noncomputable def nb097AlphaDummy044 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097AlphaDummy002 C F))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb097_alpha_dummy_045`. -/
@[expose]
noncomputable def nb097AlphaDummy045 (C : Class) (k : Var) (m : Var) (F : Class) :
    Var :=
  (freshVar (((Class.cv (nb097AlphaDummy003 C k m F))).fv) 0)

theorem nb097_fresh_000 (C : Class) (F : Class) :
    (nb097AlphaDummy004 C F) ∉
      (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
            (Class.cab (nb097AlphaDummy001 C F) (synWa
                (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                  (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                    (Class.cv (nb097AlphaDummy000 C F))))))
            (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv) :=
  by
  simpa only [nb097AlphaDummy004] using
    freshVar_not_mem
      (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
            (Class.cab (nb097AlphaDummy001 C F) (synWa
                (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                  (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                    (Class.cv (nb097AlphaDummy000 C F))))))
            (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv)
      0

theorem nb097_fresh_001 (C : Class) (F : Class) :
    (nb097AlphaDummy005 C F) ∉
      (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
            (Class.cab (nb097AlphaDummy001 C F) (synWa
                (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                  (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                    (Class.cv (nb097AlphaDummy000 C F))))))
            (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv) :=
  by
  simpa only [nb097AlphaDummy005] using
    freshVar_not_mem
      (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
            (Class.cab (nb097AlphaDummy001 C F) (synWa
                (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                  (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                    (Class.cv (nb097AlphaDummy000 C F))))))
            (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv)
      1

theorem nb097_distinct_002 (C : Class) (F : Class) :
    (nb097AlphaDummy004 C F) ≠ (nb097AlphaDummy005 C F) := by
  simpa only [nb097AlphaDummy004, nb097AlphaDummy005] using
    (freshVar_injective (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
            (Class.cab (nb097AlphaDummy001 C F) (synWa
                (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                  (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                    (Class.cv (nb097AlphaDummy000 C F))))))
            (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb097_fresh_003 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy006 C k m F) ∉
      (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
              (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
            (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv) :=
  by
  simpa only [nb097AlphaDummy006] using
    freshVar_not_mem
      (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
              (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
            (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv)
      0

theorem nb097_fresh_004 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy007 C k m F) ∉
      (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
              (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
            (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv) :=
  by
  simpa only [nb097AlphaDummy007] using
    freshVar_not_mem
      (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
              (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
            (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv)
      1

theorem nb097_distinct_005 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy006 C k m F) ≠ (nb097AlphaDummy007 C k m F) := by
  simpa only [nb097AlphaDummy006, nb097AlphaDummy007] using
    (freshVar_injective (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
              (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
            (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb097_fresh_006 (C : Class) (F : Class) :
    (nb097AlphaDummy038 C F) ∉
      (((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb097AlphaDummy038] using
    freshVar_not_mem
      (((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb097_fresh_007 (C : Class) (F : Class) :
    (nb097AlphaDummy014 C F) ∉
      (((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCphi (Class.cv (nb097AlphaDummy009 C F))))))).fv ∪
        ((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCphi (Class.cv (nb097AlphaDummy009 C F))))))).fv) :=
  by
  simpa only [nb097AlphaDummy014] using
    freshVar_not_mem
      (((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCphi (Class.cv (nb097AlphaDummy009 C F))))))).fv ∪
        ((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCphi (Class.cv (nb097AlphaDummy009 C F))))))).fv)
      0

theorem nb097_fresh_008 (k : Var) (m : Var) :
    (nb097AlphaDummy039 k m) ∉
      (((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb097AlphaDummy039] using
    freshVar_not_mem
      (((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb097_fresh_009 (k : Var) (m : Var) :
    (nb097AlphaDummy015 k m) ∉
      (((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCphi (Class.cv (nb097AlphaDummy011 k m))))))).fv ∪
        ((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCphi (Class.cv (nb097AlphaDummy011 k m))))))).fv) :=
  by
  simpa only [nb097AlphaDummy015] using
    freshVar_not_mem
      (((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCphi (Class.cv (nb097AlphaDummy011 k m))))))).fv ∪
        ((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCphi (Class.cv (nb097AlphaDummy011 k m))))))).fv)
      0

theorem nb097_fresh_010 (C : Class) (F : Class) :
    (nb097AlphaDummy008 C F) ∉
      (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy000 C F))).fv) :=
  by
  simpa only [nb097AlphaDummy008] using
    freshVar_not_mem
      (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy000 C F))).fv)
      0

theorem nb097_fresh_011 (C : Class) (F : Class) :
    (nb097AlphaDummy009 C F) ∉
      (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy000 C F))).fv) :=
  by
  simpa only [nb097AlphaDummy009] using
    freshVar_not_mem
      (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy000 C F))).fv)
      1

theorem nb097_distinct_012 (C : Class) (F : Class) :
    (nb097AlphaDummy008 C F) ≠ (nb097AlphaDummy009 C F) := by
  simpa only [nb097AlphaDummy008, nb097AlphaDummy009] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy000 C F))).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_013 (C : Class) (F : Class) :
    (nb097AlphaDummy044 C F) ∉ (((Class.cv (nb097AlphaDummy002 C F))).fv) := by
  simpa only [nb097AlphaDummy044] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy002 C F))).fv) 0

theorem nb097_fresh_014 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy045 C k m F) ∉ (((Class.cv (nb097AlphaDummy003 C k m F))).fv) :=
  by
  simpa only [nb097AlphaDummy045] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy003 C k m F))).fv) 0

theorem nb097_fresh_015 (C : Class) (F : Class) :
    (nb097AlphaDummy016 C F) ∉ (((Class.cv (nb097AlphaDummy009 C F))).fv) := by
  simpa only [nb097AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy009 C F))).fv) 0

theorem nb097_fresh_016 (C : Class) (F : Class) :
    (nb097AlphaDummy017 C F) ∉ (((Class.cv (nb097AlphaDummy009 C F))).fv) := by
  simpa only [nb097AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy009 C F))).fv) 1

theorem nb097_distinct_017 (C : Class) (F : Class) :
    (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy017 C F) := by
  simpa only [nb097AlphaDummy016, nb097AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy009 C F))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb097_fresh_018 (k : Var) (m : Var) :
    (nb097AlphaDummy018 k m) ∉ (((Class.cv (nb097AlphaDummy011 k m))).fv) := by
  simpa only [nb097AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy011 k m))).fv) 0

theorem nb097_fresh_019 (k : Var) (m : Var) :
    (nb097AlphaDummy019 k m) ∉ (((Class.cv (nb097AlphaDummy011 k m))).fv) := by
  simpa only [nb097AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy011 k m))).fv) 1

theorem nb097_distinct_020 (k : Var) (m : Var) :
    (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy019 k m) := by
  simpa only [nb097AlphaDummy018, nb097AlphaDummy019] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy011 k m))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb097_fresh_021 (C : Class) (F : Class) :
    (nb097AlphaDummy022 C F) ∉
      (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb097AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) 0

theorem nb097_fresh_022 (C : Class) (F : Class) :
    (nb097AlphaDummy023 C F) ∉
      (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb097AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) 1

theorem nb097_fresh_023 (C : Class) (F : Class) :
    (nb097AlphaDummy024 C F) ∉
      (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb097AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) 2

theorem nb097_distinct_024 (C : Class) (F : Class) :
    (nb097AlphaDummy022 C F) ≠ (nb097AlphaDummy023 C F) := by
  simpa only [nb097AlphaDummy022, nb097AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb097_distinct_025 (C : Class) (F : Class) :
    (nb097AlphaDummy022 C F) ≠ (nb097AlphaDummy024 C F) := by
  simpa only [nb097AlphaDummy022, nb097AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb097_distinct_026 (C : Class) (F : Class) :
    (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy024 C F) := by
  simpa only [nb097AlphaDummy023, nb097AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb097_fresh_027 (k : Var) (m : Var) :
    (nb097AlphaDummy025 k m) ∉
      (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb097AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) 0

theorem nb097_fresh_028 (k : Var) (m : Var) :
    (nb097AlphaDummy026 k m) ∉
      (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb097AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) 1

theorem nb097_fresh_029 (k : Var) (m : Var) :
    (nb097AlphaDummy027 k m) ∉
      (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb097AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) 2

theorem nb097_distinct_030 (k : Var) (m : Var) :
    (nb097AlphaDummy025 k m) ≠ (nb097AlphaDummy026 k m) := by
  simpa only [nb097AlphaDummy025, nb097AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb097_distinct_031 (k : Var) (m : Var) :
    (nb097AlphaDummy025 k m) ≠ (nb097AlphaDummy027 k m) := by
  simpa only [nb097AlphaDummy025, nb097AlphaDummy027] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb097_distinct_032 (k : Var) (m : Var) :
    (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy027 k m) := by
  simpa only [nb097AlphaDummy026, nb097AlphaDummy027] using
    (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb097_fresh_033 (C : Class) (F : Class) :
    (nb097AlphaDummy034 C F) ∉
      (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy023 C F))).fv) :=
  by
  simpa only [nb097AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy023 C F))).fv)
      0

theorem nb097_fresh_034 (C : Class) (F : Class) :
    (nb097AlphaDummy030 C F) ∉
      (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy024 C F))).fv) :=
  by
  simpa only [nb097AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy024 C F))).fv)
      0

theorem nb097_fresh_035 (C : Class) (F : Class) :
    (nb097AlphaDummy036 C F) ∉
      (((Class.cv (nb097AlphaDummy024 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy024 C F))).fv) :=
  by
  simpa only [nb097AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb097AlphaDummy024 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy024 C F))).fv)
      0

theorem nb097_fresh_036 (k : Var) (m : Var) :
    (nb097AlphaDummy035 k m) ∉
      (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy026 k m))).fv) :=
  by
  simpa only [nb097AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy026 k m))).fv)
      0

theorem nb097_fresh_037 (k : Var) (m : Var) :
    (nb097AlphaDummy031 k m) ∉
      (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy027 k m))).fv) :=
  by
  simpa only [nb097AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy027 k m))).fv)
      0

theorem nb097_fresh_038 (k : Var) (m : Var) :
    (nb097AlphaDummy037 k m) ∉
      (((Class.cv (nb097AlphaDummy027 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy027 k m))).fv) :=
  by
  simpa only [nb097AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb097AlphaDummy027 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy027 k m))).fv)
      0

theorem nb097_fresh_039 (k : Var) (m : Var) :
    (nb097AlphaDummy010 k m) ∉ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) := by
  simpa only [nb097AlphaDummy010] using
    freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 0

theorem nb097_fresh_040 (k : Var) (m : Var) :
    (nb097AlphaDummy011 k m) ∉ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) := by
  simpa only [nb097AlphaDummy011] using
    freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 1

theorem nb097_distinct_041 (k : Var) (m : Var) :
    (nb097AlphaDummy010 k m) ≠ (nb097AlphaDummy011 k m) := by
  simpa only [nb097AlphaDummy010, nb097AlphaDummy011] using
    (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_042 (C : Class) (F : Class) :
    (nb097AlphaDummy020 C F) ∉
      (((Wff.classMem (Class.cv (nb097AlphaDummy016 C F)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb097AlphaDummy016 C F)) (synC1c))).fv ∪
        ((Class.cv (nb097AlphaDummy016 C F))).fv) :=
  by
  simpa only [nb097AlphaDummy020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb097AlphaDummy016 C F)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb097AlphaDummy016 C F)) (synC1c))).fv ∪
        ((Class.cv (nb097AlphaDummy016 C F))).fv)
      0

theorem nb097_fresh_043 (k : Var) (m : Var) :
    (nb097AlphaDummy021 k m) ∉
      (((Wff.classMem (Class.cv (nb097AlphaDummy018 k m)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb097AlphaDummy018 k m)) (synC1c))).fv ∪
        ((Class.cv (nb097AlphaDummy018 k m))).fv) :=
  by
  simpa only [nb097AlphaDummy021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb097AlphaDummy018 k m)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb097AlphaDummy018 k m)) (synC1c))).fv ∪
        ((Class.cv (nb097AlphaDummy018 k m))).fv)
      0

theorem nb097_fresh_044 (C : Class) (F : Class) :
    (nb097AlphaDummy012 C F) ∉
      (((synCcompl (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCphi (Class.cv (nb097AlphaDummy009 C F)))))))).fv ∪ ((synCcompl
            (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb097AlphaDummy012] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCphi (Class.cv (nb097AlphaDummy009 C F)))))))).fv ∪ ((synCcompl
            (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb097_fresh_045 (k : Var) (m : Var) :
    (nb097AlphaDummy013 k m) ∉
      (((synCcompl (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCphi (Class.cv (nb097AlphaDummy011 k m)))))))).fv ∪ ((synCcompl
            (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb097AlphaDummy013] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCphi (Class.cv (nb097AlphaDummy011 k m)))))))).fv ∪ ((synCcompl
            (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb097_fresh_046 (C : Class) (F : Class) :
    (nb097AlphaDummy032 C F) ∉
      (((synCcompl (Class.cv (nb097AlphaDummy023 C F)))).fv ∪
        ((synCcompl (Class.cv (nb097AlphaDummy024 C F)))).fv) :=
  by
  simpa only [nb097AlphaDummy032] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb097AlphaDummy023 C F)))).fv ∪
        ((synCcompl (Class.cv (nb097AlphaDummy024 C F)))).fv)
      0

theorem nb097_fresh_047 (k : Var) (m : Var) :
    (nb097AlphaDummy033 k m) ∉
      (((synCcompl (Class.cv (nb097AlphaDummy026 k m)))).fv ∪
        ((synCcompl (Class.cv (nb097AlphaDummy027 k m)))).fv) :=
  by
  simpa only [nb097AlphaDummy033] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb097AlphaDummy026 k m)))).fv ∪
        ((synCcompl (Class.cv (nb097AlphaDummy027 k m)))).fv)
      0

theorem nb097_fresh_048 (C : Class) (F : Class) :
    (nb097AlphaDummy040 C F) ∉
      (((synCcompl (synCphi (Class.cv (nb097AlphaDummy009 C F))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb097AlphaDummy040] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb097AlphaDummy009 C F))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb097_fresh_049 (k : Var) (m : Var) :
    (nb097AlphaDummy041 k m) ∉
      (((synCcompl (synCphi (Class.cv (nb097AlphaDummy011 k m))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb097AlphaDummy041] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb097AlphaDummy011 k m))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb097_fresh_050 (C : Class) (F : Class) :
    (nb097AlphaDummy028 C F) ∉
      (((synCnin (Class.cv (nb097AlphaDummy023 C F))
            (Class.cv (nb097AlphaDummy024 C F)))).fv ∪
        ((synCnin (Class.cv (nb097AlphaDummy023 C F))
            (Class.cv (nb097AlphaDummy024 C F)))).fv) :=
  by
  simpa only [nb097AlphaDummy028] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb097AlphaDummy023 C F))
            (Class.cv (nb097AlphaDummy024 C F)))).fv ∪
        ((synCnin (Class.cv (nb097AlphaDummy023 C F))
            (Class.cv (nb097AlphaDummy024 C F)))).fv)
      0

theorem nb097_fresh_051 (k : Var) (m : Var) :
    (nb097AlphaDummy029 k m) ∉
      (((synCnin (Class.cv (nb097AlphaDummy026 k m))
            (Class.cv (nb097AlphaDummy027 k m)))).fv ∪
        ((synCnin (Class.cv (nb097AlphaDummy026 k m))
            (Class.cv (nb097AlphaDummy027 k m)))).fv) :=
  by
  simpa only [nb097AlphaDummy029] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb097AlphaDummy026 k m))
            (Class.cv (nb097AlphaDummy027 k m)))).fv ∪
        ((synCnin (Class.cv (nb097AlphaDummy026 k m))
            (Class.cv (nb097AlphaDummy027 k m)))).fv)
      0

theorem nb097_fresh_052 (C : Class) (F : Class) :
    (nb097AlphaDummy042 C F) ∉
      (((synCphi (Class.cv (nb097AlphaDummy009 C F)))).fv ∪
        ((synCphi (Class.cv (nb097AlphaDummy009 C F)))).fv) :=
  by
  simpa only [nb097AlphaDummy042] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb097AlphaDummy009 C F)))).fv ∪
        ((synCphi (Class.cv (nb097AlphaDummy009 C F)))).fv)
      0

theorem nb097_fresh_053 (k : Var) (m : Var) :
    (nb097AlphaDummy043 k m) ∉
      (((synCphi (Class.cv (nb097AlphaDummy011 k m)))).fv ∪
        ((synCphi (Class.cv (nb097AlphaDummy011 k m)))).fv) :=
  by
  simpa only [nb097AlphaDummy043] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb097AlphaDummy011 k m)))).fv ∪
        ((synCphi (Class.cv (nb097AlphaDummy011 k m)))).fv)
      0

theorem nb097_fresh_054 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∉ ((F).fv ∪ (C).fv) := by
  simpa only [nb097AlphaDummy000] using freshVar_not_mem ((F).fv ∪ (C).fv) 0

theorem nb097_fresh_055 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∉ ((F).fv ∪ (C).fv) := by
  simpa only [nb097AlphaDummy001] using freshVar_not_mem ((F).fv ∪ (C).fv) 1

theorem nb097_distinct_056 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy001 C F) := by
  simpa only [nb097AlphaDummy000, nb097AlphaDummy001] using
    (freshVar_injective ((F).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_057 (C : Class) (F : Class) :
    (nb097AlphaDummy002 C F) ∉
      (({(nb097AlphaDummy001 C F)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F)))))).fv) :=
  by
  simpa only [nb097AlphaDummy002] using
    freshVar_not_mem
      (({(nb097AlphaDummy001 C F)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F)))))).fv)
      0

theorem nb097_fresh_058 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy003 C k m F) ∉
      (({ m } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C)
              (synWbr (Class.cv m) (synClec) (Class.cv k))))).fv) :=
  by
  simpa only [nb097AlphaDummy003] using
    freshVar_not_mem
      (({ m } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k))))).fv)
      0

theorem nb097_support_mem_0000 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∈
      (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy000 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0001 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∈
      (((synCcompl (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCphi (Class.cv (nb097AlphaDummy009 C F)))))))).fv ∪ ((synCcompl
            (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy008 C F) from (by
          unfold nb097AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy009 C F) from (by
            unfold nb097AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0002 (k : Var) (m : Var) :
    m ∈ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0003 (k : Var) (m : Var) :
    m ∈
      (((synCcompl (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCphi (Class.cv (nb097AlphaDummy011 k m)))))))).fv ∪ ((synCcompl
            (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb097AlphaDummy010 k m) from (by
          unfold nb097AlphaDummy010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb097AlphaDummy011 k m) from (by
            unfold nb097AlphaDummy011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0004 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∈
      (((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCphi (Class.cv (nb097AlphaDummy009 C F))))))).fv ∪
        ((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCphi (Class.cv (nb097AlphaDummy009 C F))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy008 C F) from (by
          unfold nb097AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy009 C F) from (by
            unfold nb097AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0005 (k : Var) (m : Var) :
    m ∈
      (((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCphi (Class.cv (nb097AlphaDummy011 k m))))))).fv ∪
        ((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCphi (Class.cv (nb097AlphaDummy011 k m))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb097AlphaDummy010 k m) from (by
          unfold nb097AlphaDummy010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb097AlphaDummy011 k m) from (by
            unfold nb097AlphaDummy011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0006 (C : Class) (F : Class) :
    (nb097AlphaDummy009 C F) ∈ (((Class.cv (nb097AlphaDummy009 C F))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0007 (k : Var) (m : Var) :
    (nb097AlphaDummy011 k m) ∈ (((Class.cv (nb097AlphaDummy011 k m))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0008 (C : Class) (F : Class) :
    (nb097AlphaDummy016 C F) ∈
      (((Wff.classMem (Class.cv (nb097AlphaDummy016 C F)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb097AlphaDummy016 C F)) (synC1c))).fv ∪
        ((Class.cv (nb097AlphaDummy016 C F))).fv) :=
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

theorem nb097_support_mem_0009 (k : Var) (m : Var) :
    (nb097AlphaDummy018 k m) ∈
      (((Wff.classMem (Class.cv (nb097AlphaDummy018 k m)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb097AlphaDummy018 k m)) (synC1c))).fv ∪
        ((Class.cv (nb097AlphaDummy018 k m))).fv) :=
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

theorem nb097_support_mem_0010 (C : Class) (F : Class) :
    (nb097AlphaDummy016 C F) ∈
      (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0011 (k : Var) (m : Var) :
    (nb097AlphaDummy018 k m) ∈
      (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0012 (C : Class) (F : Class) :
    (nb097AlphaDummy023 C F) ∈
      (((synCnin (Class.cv (nb097AlphaDummy023 C F))
            (Class.cv (nb097AlphaDummy024 C F)))).fv ∪
        ((synCnin (Class.cv (nb097AlphaDummy023 C F))
            (Class.cv (nb097AlphaDummy024 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0013 (k : Var) (m : Var) :
    (nb097AlphaDummy026 k m) ∈
      (((synCnin (Class.cv (nb097AlphaDummy026 k m))
            (Class.cv (nb097AlphaDummy027 k m)))).fv ∪
        ((synCnin (Class.cv (nb097AlphaDummy026 k m))
            (Class.cv (nb097AlphaDummy027 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0014 (C : Class) (F : Class) :
    (nb097AlphaDummy023 C F) ∈
      (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy024 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0015 (k : Var) (m : Var) :
    (nb097AlphaDummy026 k m) ∈
      (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy027 k m))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0016 (C : Class) (F : Class) :
    (nb097AlphaDummy024 C F) ∈
      (((synCnin (Class.cv (nb097AlphaDummy023 C F))
            (Class.cv (nb097AlphaDummy024 C F)))).fv ∪
        ((synCnin (Class.cv (nb097AlphaDummy023 C F))
            (Class.cv (nb097AlphaDummy024 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0017 (k : Var) (m : Var) :
    (nb097AlphaDummy027 k m) ∈
      (((synCnin (Class.cv (nb097AlphaDummy026 k m))
            (Class.cv (nb097AlphaDummy027 k m)))).fv ∪
        ((synCnin (Class.cv (nb097AlphaDummy026 k m))
            (Class.cv (nb097AlphaDummy027 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0018 (C : Class) (F : Class) :
    (nb097AlphaDummy024 C F) ∈
      (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy024 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0019 (k : Var) (m : Var) :
    (nb097AlphaDummy027 k m) ∈
      (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy027 k m))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0020 (C : Class) (F : Class) :
    (nb097AlphaDummy023 C F) ∈
      (((synCcompl (Class.cv (nb097AlphaDummy023 C F)))).fv ∪
        ((synCcompl (Class.cv (nb097AlphaDummy024 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0021 (k : Var) (m : Var) :
    (nb097AlphaDummy026 k m) ∈
      (((synCcompl (Class.cv (nb097AlphaDummy026 k m)))).fv ∪
        ((synCcompl (Class.cv (nb097AlphaDummy027 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0022 (C : Class) (F : Class) :
    (nb097AlphaDummy023 C F) ∈
      (((Class.cv (nb097AlphaDummy023 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy023 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0023 (k : Var) (m : Var) :
    (nb097AlphaDummy026 k m) ∈
      (((Class.cv (nb097AlphaDummy026 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy026 k m))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0024 (C : Class) (F : Class) :
    (nb097AlphaDummy024 C F) ∈
      (((synCcompl (Class.cv (nb097AlphaDummy023 C F)))).fv ∪
        ((synCcompl (Class.cv (nb097AlphaDummy024 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0025 (k : Var) (m : Var) :
    (nb097AlphaDummy027 k m) ∈
      (((synCcompl (Class.cv (nb097AlphaDummy026 k m)))).fv ∪
        ((synCcompl (Class.cv (nb097AlphaDummy027 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0026 (C : Class) (F : Class) :
    (nb097AlphaDummy024 C F) ∈
      (((Class.cv (nb097AlphaDummy024 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy024 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0027 (k : Var) (m : Var) :
    (nb097AlphaDummy027 k m) ∈
      (((Class.cv (nb097AlphaDummy027 k m))).fv ∪
        ((Class.cv (nb097AlphaDummy027 k m))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0028 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∈
      (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
        ((Class.cv (nb097AlphaDummy000 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0029 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∈
      (((synCcompl (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCphi (Class.cv (nb097AlphaDummy009 C F)))))))).fv ∪ ((synCcompl
            (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy008 C F) from (by
          unfold nb097AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy009 C F) from (by
            unfold nb097AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0030 (k : Var) (m : Var) :
    k ∈ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0031 (k : Var) (m : Var) :
    k ∈
      (((synCcompl (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCphi (Class.cv (nb097AlphaDummy011 k m)))))))).fv ∪ ((synCcompl
            (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show k ≠ (nb097AlphaDummy010 k m) from (by
          unfold nb097AlphaDummy010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show k ≠ (nb097AlphaDummy011 k m) from (by
            unfold nb097AlphaDummy011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0032 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∈
      (((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb097AlphaDummy008 C F)
            (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy000 C F))
              (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy008 C F) from (by
          unfold nb097AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy009 C F) from (by
            unfold nb097AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0033 (k : Var) (m : Var) :
    k ∈
      (((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb097AlphaDummy010 k m)
            (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show k ≠ (nb097AlphaDummy010 k m) from (by
          unfold nb097AlphaDummy010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show k ≠ (nb097AlphaDummy011 k m) from (by
            unfold nb097AlphaDummy011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0034 (C : Class) (F : Class) :
    (nb097AlphaDummy009 C F) ∈
      (((synCcompl (synCphi (Class.cv (nb097AlphaDummy009 C F))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0035 (k : Var) (m : Var) :
    (nb097AlphaDummy011 k m) ∈
      (((synCcompl (synCphi (Class.cv (nb097AlphaDummy011 k m))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0036 (C : Class) (F : Class) :
    (nb097AlphaDummy009 C F) ∈
      (((synCphi (Class.cv (nb097AlphaDummy009 C F)))).fv ∪
        ((synCphi (Class.cv (nb097AlphaDummy009 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0037 (k : Var) (m : Var) :
    (nb097AlphaDummy011 k m) ∈
      (((synCphi (Class.cv (nb097AlphaDummy011 k m)))).fv ∪
        ((synCphi (Class.cv (nb097AlphaDummy011 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0038 (C : Class) (F : Class) :
    (nb097AlphaDummy002 C F) ∈ (((Class.cv (nb097AlphaDummy002 C F))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0039 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy003 C k m F) ∈ (((Class.cv (nb097AlphaDummy003 C k m F))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_focused_notmem_0000 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∉ C.fv :=
  by
  change freshVar ((F).fv ∪ (C).fv) 1 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb097_focused_notmem_0001 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∉ F.fv :=
  by
  change freshVar ((F).fv ∪ (C).fv) 1 ∉ F.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb097_wpp_notmem_0000 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∉ ((synCwppcand F C)).fv := by
  simpa only [nb097AlphaDummy001, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0000 C F) (nb097_focused_notmem_0001 C F))

theorem nb097_wpp_notmem_0001 (C : Class) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv)
    (dv_F_m : m ∉ F.fv) : m ∉ ((synCwppcand F C)).fv := by
  simpa only [fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro dv_C_m dv_F_m)

theorem nb097_focused_notmem_0002 (C : Class) (F : Class) :
    (nb097AlphaDummy002 C F) ∉ C.fv :=
  by
  change
    freshVar
        (({(nb097AlphaDummy001 C F)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
              (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                  (Class.cv (nb097AlphaDummy000 C F)))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
      (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
        (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
          (Class.cv (nb097AlphaDummy000 C F))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cwppcand F C]
  rw [Finset.mem_union]
  left
  exact hu


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

theorem nb097_focused_notmem_0003 (C : Class) (F : Class) :
    (nb097AlphaDummy002 C F) ∉ F.fv :=
  by
  change
    freshVar
        (({(nb097AlphaDummy001 C F)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
              (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                  (Class.cv (nb097AlphaDummy000 C F)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
      (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
        (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
          (Class.cv (nb097AlphaDummy000 C F))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cwppcand F C]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb097_wpp_notmem_0002 (C : Class) (F : Class) :
    (nb097AlphaDummy002 C F) ∉ ((synCwppcand F C)).fv := by
  simpa only [nb097AlphaDummy002, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0002 C F) (nb097_focused_notmem_0003 C F))

theorem nb097_focused_notmem_0004 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy003 C k m F) ∉ C.fv :=
  by
  change
    freshVar
        (({ m } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
              (synWral k (synCwppcand F C)
                (synWbr (Class.cv m) (synClec) (Class.cv k))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv m) (synCwppcand F C))
      (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv m) (synCwppcand F C)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cwppcand F C]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb097_focused_notmem_0005 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy003 C k m F) ∉ F.fv :=
  by
  change
    freshVar
        (({ m } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
              (synWral k (synCwppcand F C)
                (synWbr (Class.cv m) (synClec) (Class.cv k))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv m) (synCwppcand F C))
      (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv m) (synCwppcand F C)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cwppcand F C]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb097_wpp_notmem_0003 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy003 C k m F) ∉ ((synCwppcand F C)).fv := by
  simpa only [nb097AlphaDummy003, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0004 C k m F) (nb097_focused_notmem_0005 C k m F))

theorem nb097_focused_notmem_0006 (C : Class) (F : Class) :
    (nb097AlphaDummy005 C F) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
              (Class.cab (nb097AlphaDummy001 C F) (synWa
                  (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                  (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                    (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                      (Class.cv (nb097AlphaDummy000 C F))))))
              (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv)
        1 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097AlphaDummy002 C F)
      (Wff.classEq (Class.cab (nb097AlphaDummy001 C F)
          (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F))))))
        (synCsn (Class.cv (nb097AlphaDummy002 C F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0002 C F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb097AlphaDummy001 C F)
          (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F))))))
        (synCsn (Class.cv (nb097AlphaDummy002 C F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb097AlphaDummy001 C F)
        (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F)))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb097_focused_notmem_0000 C F)) (h_eq ▸ hu)
    · rw [fv_syn_wa
          (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F))))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb097_focused_notmem_0007 (C : Class) (F : Class) :
    (nb097AlphaDummy005 C F) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
              (Class.cab (nb097AlphaDummy001 C F) (synWa
                  (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                  (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                    (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                      (Class.cv (nb097AlphaDummy000 C F))))))
              (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097AlphaDummy002 C F)
      (Wff.classEq (Class.cab (nb097AlphaDummy001 C F)
          (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F))))))
        (synCsn (Class.cv (nb097AlphaDummy002 C F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0003 C F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb097AlphaDummy001 C F)
          (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F))))))
        (synCsn (Class.cv (nb097AlphaDummy002 C F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb097AlphaDummy001 C F)
        (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F)))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb097_focused_notmem_0001 C F)) (h_eq ▸ hu)
    · rw [fv_syn_wa
          (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F))))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb097_wpp_notmem_0004 (C : Class) (F : Class) :
    (nb097AlphaDummy005 C F) ∉ ((synCwppcand F C)).fv := by
  simpa only [nb097AlphaDummy005, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0006 C F) (nb097_focused_notmem_0007 C F))

theorem nb097_focused_notmem_0008 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) : (nb097AlphaDummy007 C k m F) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
                (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                  (synWral k (synCwppcand F C)
                    (synWbr (Class.cv m) (synClec) (Class.cv k)))))
              (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv)
        1 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097AlphaDummy003 C k m F)
      (Wff.classEq (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
        (synCsn (Class.cv (nb097AlphaDummy003 C k m F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0004 C k m F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
        (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab m
        (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_C_m) (h_eq ▸ hu)
    · rw [fv_syn_wa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv m) (synCwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb097_focused_notmem_0009 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_F_m : m ∉ F.fv) : (nb097AlphaDummy007 C k m F) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
                (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                  (synWral k (synCwppcand F C)
                    (synWbr (Class.cv m) (synClec) (Class.cv k)))))
              (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097AlphaDummy003 C k m F)
      (Wff.classEq (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
        (synCsn (Class.cv (nb097AlphaDummy003 C k m F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0005 C k m F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
        (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab m
        (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_F_m) (h_eq ▸ hu)
    · rw [fv_syn_wa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv m) (synCwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb097_wpp_notmem_0005 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) :
    (nb097AlphaDummy007 C k m F) ∉ ((synCwppcand F C)).fv := by
  simpa only [nb097AlphaDummy007, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0008 C k m F dv_C_m)
      (nb097_focused_notmem_0009 C k m F dv_F_m))

theorem nb097_focused_notmem_0010 (C : Class) (F : Class) :
    (nb097AlphaDummy004 C F) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
              (Class.cab (nb097AlphaDummy001 C F) (synWa
                  (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                  (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                    (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                      (Class.cv (nb097AlphaDummy000 C F))))))
              (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097AlphaDummy002 C F)
      (Wff.classEq (Class.cab (nb097AlphaDummy001 C F)
          (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F))))))
        (synCsn (Class.cv (nb097AlphaDummy002 C F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0002 C F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb097AlphaDummy001 C F)
          (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F))))))
        (synCsn (Class.cv (nb097AlphaDummy002 C F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb097AlphaDummy001 C F)
        (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F)))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb097_focused_notmem_0000 C F)) (h_eq ▸ hu)
    · rw [fv_syn_wa
          (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F))))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb097_focused_notmem_0011 (C : Class) (F : Class) :
    (nb097AlphaDummy004 C F) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
              (Class.cab (nb097AlphaDummy001 C F) (synWa
                  (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
                  (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                    (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                      (Class.cv (nb097AlphaDummy000 C F))))))
              (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097AlphaDummy002 C F)
      (Wff.classEq (Class.cab (nb097AlphaDummy001 C F)
          (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F))))))
        (synCsn (Class.cv (nb097AlphaDummy002 C F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0003 C F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb097AlphaDummy001 C F)
          (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                (Class.cv (nb097AlphaDummy000 C F))))))
        (synCsn (Class.cv (nb097AlphaDummy002 C F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb097AlphaDummy001 C F)
        (synWa (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F)))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb097_focused_notmem_0001 C F)) (h_eq ▸ hu)
    · rw [fv_syn_wa
          (Wff.classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C))
          (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
            (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
              (Class.cv (nb097AlphaDummy000 C F))))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv (nb097AlphaDummy001 C F)) (synCwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb097_wpp_notmem_0006 (C : Class) (F : Class) :
    (nb097AlphaDummy004 C F) ∉ ((synCwppcand F C)).fv := by
  simpa only [nb097AlphaDummy004, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0010 C F) (nb097_focused_notmem_0011 C F))

theorem nb097_focused_notmem_0012 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) : (nb097AlphaDummy006 C k m F) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
                (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                  (synWral k (synCwppcand F C)
                    (synWbr (Class.cv m) (synClec) (Class.cv k)))))
              (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097AlphaDummy003 C k m F)
      (Wff.classEq (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
        (synCsn (Class.cv (nb097AlphaDummy003 C k m F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0004 C k m F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
        (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab m
        (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_C_m) (h_eq ▸ hu)
    · rw [fv_syn_wa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv m) (synCwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb097_focused_notmem_0013 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_F_m : m ∉ F.fv) : (nb097AlphaDummy006 C k m F) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq (Class.cab m
                (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                  (synWral k (synCwppcand F C)
                    (synWbr (Class.cv m) (synClec) (Class.cv k)))))
              (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097AlphaDummy003 C k m F)
      (Wff.classEq (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
        (synCsn (Class.cv (nb097AlphaDummy003 C k m F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0005 C k m F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))))
        (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab m
        (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_F_m) (h_eq ▸ hu)
    · rw [fv_syn_wa (Wff.classMem (Class.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (Class.cv m) (synClec) (Class.cv k)))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv m) (synCwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb097_wpp_notmem_0007 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) :
    (nb097AlphaDummy006 C k m F) ∉ ((synCwppcand F C)).fv := by
  simpa only [nb097AlphaDummy006, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0012 C k m F dv_C_m)
      (nb097_focused_notmem_0013 C k m F dv_F_m))

theorem nb097_compact_envfresh_0000 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) :
    TEnvFresh
      [((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
      ((synCwppcand F C)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb097AlphaDummy001 C F) m (nb097_wpp_notmem_0000 C F)
      (nb097_wpp_notmem_0001 C m F dv_C_m dv_F_m)
      (TEnvFresh.consFresh (nb097AlphaDummy002 C F) (nb097AlphaDummy003 C k m F)
        (nb097_wpp_notmem_0002 C F) (nb097_wpp_notmem_0003 C k m F)
        (TEnvFresh.consFresh (nb097AlphaDummy005 C F) (nb097AlphaDummy007 C k m F)
          (nb097_wpp_notmem_0004 C F) (nb097_wpp_notmem_0005 C k m F dv_C_m dv_F_m)
          (TEnvFresh.consFresh (nb097AlphaDummy004 C F) (nb097AlphaDummy006 C k m F)
            (nb097_wpp_notmem_0006 C F) (nb097_wpp_notmem_0007 C k m F dv_C_m dv_F_m)
            (TEnvFresh.nil ((synCwppcand F C)).fv)))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C097M3Part001Stage2`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb097_wpp_refl_0000`. -/
@[expose]
noncomputable def nb097WppRefl0000 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) :
    TReflOn
      [((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
      ((synCwppcand F C)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0000 C k m F dv_C_m dv_F_m)

theorem nb097_focused_notmem_0014 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∉ C.fv :=
  by
  change freshVar ((F).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb097_focused_notmem_0015 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∉ F.fv :=
  by
  change freshVar ((F).fv ∪ (C).fv) 0 ∉ F.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb097_wpp_notmem_0008 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∉ ((synCwppcand F C)).fv := by
  simpa only [nb097AlphaDummy000, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0014 C F) (nb097_focused_notmem_0015 C F))

theorem nb097_wpp_notmem_0009 (C : Class) (k : Var) (F : Class) (dv_C_k : k ∉ C.fv)
    (dv_F_k : k ∉ F.fv) : k ∉ ((synCwppcand F C)).fv := by
  simpa only [fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro dv_C_k dv_F_k)

theorem nb097_compact_envfresh_0001 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) :
    TEnvFresh
      [((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
      ((synCwppcand F C)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb097AlphaDummy000 C F) k (nb097_wpp_notmem_0008 C F)
      (nb097_wpp_notmem_0009 C k F dv_C_k dv_F_k)
      (TEnvFresh.consFresh (nb097AlphaDummy001 C F) m (nb097_wpp_notmem_0000 C F)
        (nb097_wpp_notmem_0001 C m F dv_C_m dv_F_m)
        (TEnvFresh.consFresh (nb097AlphaDummy002 C F) (nb097AlphaDummy003 C k m F)
          (nb097_wpp_notmem_0002 C F) (nb097_wpp_notmem_0003 C k m F)
          (TEnvFresh.consFresh (nb097AlphaDummy005 C F) (nb097AlphaDummy007 C k m F)
            (nb097_wpp_notmem_0004 C F) (nb097_wpp_notmem_0005 C k m F dv_C_m dv_F_m)
            (TEnvFresh.consFresh (nb097AlphaDummy004 C F)
              (nb097AlphaDummy006 C k m F) (nb097_wpp_notmem_0006 C F)
              (nb097_wpp_notmem_0007 C k m F dv_C_m dv_F_m)
              (TEnvFresh.nil ((synCwppcand F C)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C097M3Part001Stage3`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb097_wpp_refl_0001`. -/
@[expose]
noncomputable def nb097WppRefl0001 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) :
    TReflOn
      [((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
      ((synCwppcand F C)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0001 C k m F dv_C_k dv_C_m dv_F_k dv_F_m)

theorem nb097_compact_fv_empty_0020 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0021 (k : Var) : k ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0022 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0023 (m : Var) : m ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0024 (C : Class) (F : Class) :
    (nb097AlphaDummy002 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0025 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy003 C k m F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0026 (C : Class) (F : Class) :
    (nb097AlphaDummy005 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0027 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy007 C k m F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0028 (C : Class) (F : Class) :
    (nb097AlphaDummy004 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0029 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy006 C k m F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
