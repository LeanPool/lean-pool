/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C069C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_000`. -/
@[expose]
noncomputable def nb069AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_001`. -/
@[expose]
noncomputable def nb069AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_002`. -/
@[expose]
noncomputable def nb069AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_003`. -/
@[expose]
noncomputable def nb069AlphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_004`. -/
@[expose]
noncomputable def nb069AlphaDummy004 : Var :=
  (freshVar
    (({(nb069AlphaDummy000)} : Finset Var) ∪ ({(nb069AlphaDummy001)} : Finset Var) ∪
      ((synWrex (nb069AlphaDummy002) (Class.cv (nb069AlphaDummy000))
          (synWrex (nb069AlphaDummy003) (Class.cv (nb069AlphaDummy001))
            (synWss (Class.cv (nb069AlphaDummy002))
              (Class.cv (nb069AlphaDummy003)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_005`. -/
@[expose]
noncomputable def nb069AlphaDummy005 (x : Var) (y : Var) (a : Var) (b : Var) : Var :=
  (freshVar (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
          (synWrex y (Class.cv b) (synWss (Class.cv x) (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_006`. -/
@[expose]
noncomputable def nb069AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_007`. -/
@[expose]
noncomputable def nb069AlphaDummy007 : Var :=
  (freshVar
    (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_008`. -/
@[expose]
noncomputable def nb069AlphaDummy008 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_009`. -/
@[expose]
noncomputable def nb069AlphaDummy009 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_010`. -/
@[expose]
noncomputable def nb069AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCphi (Class.cv (nb069AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_011`. -/
@[expose]
noncomputable def nb069AlphaDummy011 (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCphi (Class.cv (nb069AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
          (Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_012`. -/
@[expose]
noncomputable def nb069AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb069AlphaDummy006)
          (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
            (Wff.classEq (Class.cv (nb069AlphaDummy006))
              (synCphi (Class.cv (nb069AlphaDummy007))))))).fv ∪
      ((Class.cab (nb069AlphaDummy006)
          (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
            (Wff.classEq (Class.cv (nb069AlphaDummy006))
              (synCphi (Class.cv (nb069AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_013`. -/
@[expose]
noncomputable def nb069AlphaDummy013 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb069AlphaDummy008 a b)
          (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
              (synCphi (Class.cv (nb069AlphaDummy009 a b))))))).fv ∪
      ((Class.cab (nb069AlphaDummy008 a b) (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
              (synCphi (Class.cv (nb069AlphaDummy009 a b))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_014`. -/
@[expose]
noncomputable def nb069AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_015`. -/
@[expose]
noncomputable def nb069AlphaDummy015 : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_016`. -/
@[expose]
noncomputable def nb069AlphaDummy016 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy009 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_017`. -/
@[expose]
noncomputable def nb069AlphaDummy017 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy009 a b))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_018`. -/
@[expose]
noncomputable def nb069AlphaDummy018 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb069AlphaDummy014)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb069AlphaDummy014)) (synC1c))).fv ∪
      ((Class.cv (nb069AlphaDummy014))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_019`. -/
@[expose]
noncomputable def nb069AlphaDummy019 (a : Var) (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb069AlphaDummy016 a b)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb069AlphaDummy016 a b)) (synC1c))).fv ∪
      ((Class.cv (nb069AlphaDummy016 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_020`. -/
@[expose]
noncomputable def nb069AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_021`. -/
@[expose]
noncomputable def nb069AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_022`. -/
@[expose]
noncomputable def nb069AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_023`. -/
@[expose]
noncomputable def nb069AlphaDummy023 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_024`. -/
@[expose]
noncomputable def nb069AlphaDummy024 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_025`. -/
@[expose]
noncomputable def nb069AlphaDummy025 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_026`. -/
@[expose]
noncomputable def nb069AlphaDummy026 : Var :=
  (freshVar (((synCnin (Class.cv (nb069AlphaDummy021))
          (Class.cv (nb069AlphaDummy022)))).fv ∪
      ((synCnin (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_027`. -/
@[expose]
noncomputable def nb069AlphaDummy027 (a : Var) (b : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb069AlphaDummy024 a b))
          (Class.cv (nb069AlphaDummy025 a b)))).fv ∪
      ((synCnin (Class.cv (nb069AlphaDummy024 a b))
          (Class.cv (nb069AlphaDummy025 a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_028`. -/
@[expose]
noncomputable def nb069AlphaDummy028 : Var :=
  (freshVar
    (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_029`. -/
@[expose]
noncomputable def nb069AlphaDummy029 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
      ((Class.cv (nb069AlphaDummy025 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_030`. -/
@[expose]
noncomputable def nb069AlphaDummy030 : Var :=
  (freshVar (((synCcompl (Class.cv (nb069AlphaDummy021)))).fv ∪
      ((synCcompl (Class.cv (nb069AlphaDummy022)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_031`. -/
@[expose]
noncomputable def nb069AlphaDummy031 (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb069AlphaDummy024 a b)))).fv ∪
      ((synCcompl (Class.cv (nb069AlphaDummy025 a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_032`. -/
@[expose]
noncomputable def nb069AlphaDummy032 : Var :=
  (freshVar
    (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_033`. -/
@[expose]
noncomputable def nb069AlphaDummy033 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
      ((Class.cv (nb069AlphaDummy024 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_034`. -/
@[expose]
noncomputable def nb069AlphaDummy034 : Var :=
  (freshVar
    (((Class.cv (nb069AlphaDummy022))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_035`. -/
@[expose]
noncomputable def nb069AlphaDummy035 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb069AlphaDummy025 a b))).fv ∪
      ((Class.cv (nb069AlphaDummy025 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_036`. -/
@[expose]
noncomputable def nb069AlphaDummy036 : Var :=
  (freshVar (((Class.cab (nb069AlphaDummy006)
          (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
            (Wff.classEq (Class.cv (nb069AlphaDummy006))
              (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb069AlphaDummy006)
          (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
            (Wff.classEq (Class.cv (nb069AlphaDummy006))
              (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_037`. -/
@[expose]
noncomputable def nb069AlphaDummy037 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb069AlphaDummy008 a b)
          (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
            (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
              (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb069AlphaDummy008 a b)
          (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
            (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
              (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_038`. -/
@[expose]
noncomputable def nb069AlphaDummy038 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb069AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_039`. -/
@[expose]
noncomputable def nb069AlphaDummy039 (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb069AlphaDummy009 a b))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_040`. -/
@[expose]
noncomputable def nb069AlphaDummy040 : Var :=
  (freshVar (((synCphi (Class.cv (nb069AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb069AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_041`. -/
@[expose]
noncomputable def nb069AlphaDummy041 (a : Var) (b : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb069AlphaDummy009 a b)))).fv ∪
      ((synCphi (Class.cv (nb069AlphaDummy009 a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_042`. -/
@[expose]
noncomputable def nb069AlphaDummy042 : Var :=
  (freshVar (((synCnin (Class.cv (nb069AlphaDummy002))
          (Class.cv (nb069AlphaDummy003)))).fv ∪
      ((synCnin (Class.cv (nb069AlphaDummy002)) (Class.cv (nb069AlphaDummy003)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_043`. -/
@[expose]
noncomputable def nb069AlphaDummy043 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv x) (Class.cv y))).fv ∪
      ((synCnin (Class.cv x) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_044`. -/
@[expose]
noncomputable def nb069AlphaDummy044 : Var :=
  (freshVar
    (((Class.cv (nb069AlphaDummy002))).fv ∪ ((Class.cv (nb069AlphaDummy003))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb069_alpha_dummy_045`. -/
@[expose]
noncomputable def nb069AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

theorem nb069_fresh_000 :
    (nb069AlphaDummy012) ∉
      (((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCphi (Class.cv (nb069AlphaDummy007))))))).fv ∪
        ((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCphi (Class.cv (nb069AlphaDummy007))))))).fv) :=
  by
  simpa only [nb069AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCphi (Class.cv (nb069AlphaDummy007))))))).fv ∪
        ((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCphi (Class.cv (nb069AlphaDummy007))))))).fv)
      0

theorem nb069_fresh_001 :
    (nb069AlphaDummy036) ∉
      (((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb069AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb069_fresh_002 (a : Var) (b : Var) :
    (nb069AlphaDummy013 a b) ∉
      (((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCphi (Class.cv (nb069AlphaDummy009 a b))))))).fv ∪
        ((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCphi (Class.cv (nb069AlphaDummy009 a b))))))).fv) :=
  by
  simpa only [nb069AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCphi (Class.cv (nb069AlphaDummy009 a b))))))).fv ∪
        ((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCphi (Class.cv (nb069AlphaDummy009 a b))))))).fv)
      0

theorem nb069_fresh_003 (a : Var) (b : Var) :
    (nb069AlphaDummy037 a b) ∉
      (((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb069AlphaDummy037] using
    freshVar_not_mem
      (((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb069_fresh_004 (a : Var) (b : Var) :
    (nb069AlphaDummy008 a b) ∉ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) := by
  simpa only [nb069AlphaDummy008] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 0

theorem nb069_fresh_005 (a : Var) (b : Var) :
    (nb069AlphaDummy009 a b) ∉ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) := by
  simpa only [nb069AlphaDummy009] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 1

theorem nb069_distinct_006 (a : Var) (b : Var) :
    (nb069AlphaDummy008 a b) ≠ (nb069AlphaDummy009 a b) := by
  simpa only [nb069AlphaDummy008, nb069AlphaDummy009] using
    (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (i := 0) (j := 1) (by decide))

theorem nb069_fresh_007 :
    (nb069AlphaDummy006) ∉
      (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv) :=
  by
  simpa only [nb069AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv)
      0

theorem nb069_fresh_008 :
    (nb069AlphaDummy007) ∉
      (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv) :=
  by
  simpa only [nb069AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv)
      1

theorem nb069_distinct_009 : (nb069AlphaDummy006) ≠ (nb069AlphaDummy007) := by
  simpa only [nb069AlphaDummy006, nb069AlphaDummy007] using
    (freshVar_injective
      (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb069_fresh_010 :
    (nb069AlphaDummy044) ∉
      (((Class.cv (nb069AlphaDummy002))).fv ∪ ((Class.cv (nb069AlphaDummy003))).fv) :=
  by
  simpa only [nb069AlphaDummy044] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy002))).fv ∪ ((Class.cv (nb069AlphaDummy003))).fv)
      0

theorem nb069_fresh_011 :
    (nb069AlphaDummy014) ∉ (((Class.cv (nb069AlphaDummy007))).fv) := by
  simpa only [nb069AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy007))).fv) 0

theorem nb069_fresh_012 :
    (nb069AlphaDummy015) ∉ (((Class.cv (nb069AlphaDummy007))).fv) := by
  simpa only [nb069AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy007))).fv) 1

theorem nb069_distinct_013 : (nb069AlphaDummy014) ≠ (nb069AlphaDummy015) := by
  simpa only [nb069AlphaDummy014, nb069AlphaDummy015] using
    (freshVar_injective (((Class.cv (nb069AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb069_fresh_014 (a : Var) (b : Var) :
    (nb069AlphaDummy016 a b) ∉ (((Class.cv (nb069AlphaDummy009 a b))).fv) := by
  simpa only [nb069AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy009 a b))).fv) 0

theorem nb069_fresh_015 (a : Var) (b : Var) :
    (nb069AlphaDummy017 a b) ∉ (((Class.cv (nb069AlphaDummy009 a b))).fv) := by
  simpa only [nb069AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy009 a b))).fv) 1

theorem nb069_distinct_016 (a : Var) (b : Var) :
    (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy017 a b) := by
  simpa only [nb069AlphaDummy016, nb069AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb069AlphaDummy009 a b))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb069_fresh_017 :
    (nb069AlphaDummy020) ∉
      (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb069AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) 0

theorem nb069_fresh_018 :
    (nb069AlphaDummy021) ∉
      (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb069AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) 1

theorem nb069_fresh_019 :
    (nb069AlphaDummy022) ∉
      (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb069AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) 2

theorem nb069_distinct_020 : (nb069AlphaDummy020) ≠ (nb069AlphaDummy021) := by
  simpa only [nb069AlphaDummy020, nb069AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb069_distinct_021 : (nb069AlphaDummy020) ≠ (nb069AlphaDummy022) := by
  simpa only [nb069AlphaDummy020, nb069AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb069_distinct_022 : (nb069AlphaDummy021) ≠ (nb069AlphaDummy022) := by
  simpa only [nb069AlphaDummy021, nb069AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb069_fresh_023 (a : Var) (b : Var) :
    (nb069AlphaDummy023 a b) ∉
      (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb069AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 0

theorem nb069_fresh_024 (a : Var) (b : Var) :
    (nb069AlphaDummy024 a b) ∉
      (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb069AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 1

theorem nb069_fresh_025 (a : Var) (b : Var) :
    (nb069AlphaDummy025 a b) ∉
      (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb069AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 2

theorem nb069_distinct_026 (a : Var) (b : Var) :
    (nb069AlphaDummy023 a b) ≠ (nb069AlphaDummy024 a b) := by
  simpa only [nb069AlphaDummy023, nb069AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb069_distinct_027 (a : Var) (b : Var) :
    (nb069AlphaDummy023 a b) ≠ (nb069AlphaDummy025 a b) := by
  simpa only [nb069AlphaDummy023, nb069AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb069_distinct_028 (a : Var) (b : Var) :
    (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy025 a b) := by
  simpa only [nb069AlphaDummy024, nb069AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb069_fresh_029 :
    (nb069AlphaDummy032) ∉
      (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy021))).fv) :=
  by
  simpa only [nb069AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy021))).fv)
      0

theorem nb069_fresh_030 :
    (nb069AlphaDummy028) ∉
      (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv) :=
  by
  simpa only [nb069AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv)
      0

theorem nb069_fresh_031 :
    (nb069AlphaDummy034) ∉
      (((Class.cv (nb069AlphaDummy022))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv) :=
  by
  simpa only [nb069AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy022))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv)
      0

theorem nb069_fresh_032 (a : Var) (b : Var) :
    (nb069AlphaDummy033 a b) ∉
      (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy024 a b))).fv) :=
  by
  simpa only [nb069AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy024 a b))).fv)
      0

theorem nb069_fresh_033 (a : Var) (b : Var) :
    (nb069AlphaDummy029 a b) ∉
      (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy025 a b))).fv) :=
  by
  simpa only [nb069AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy025 a b))).fv)
      0

theorem nb069_fresh_034 (a : Var) (b : Var) :
    (nb069AlphaDummy035 a b) ∉
      (((Class.cv (nb069AlphaDummy025 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy025 a b))).fv) :=
  by
  simpa only [nb069AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb069AlphaDummy025 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy025 a b))).fv)
      0

theorem nb069_fresh_035 (x : Var) (y : Var) :
    (nb069AlphaDummy045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb069AlphaDummy045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb069_fresh_036 :
    (nb069AlphaDummy018) ∉
      (((Wff.classMem (Class.cv (nb069AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb069AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb069AlphaDummy014))).fv) :=
  by
  simpa only [nb069AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb069AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb069AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb069AlphaDummy014))).fv)
      0

theorem nb069_fresh_037 (a : Var) (b : Var) :
    (nb069AlphaDummy019 a b) ∉
      (((Wff.classMem (Class.cv (nb069AlphaDummy016 a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb069AlphaDummy016 a b)) (synC1c))).fv ∪
        ((Class.cv (nb069AlphaDummy016 a b))).fv) :=
  by
  simpa only [nb069AlphaDummy019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb069AlphaDummy016 a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb069AlphaDummy016 a b)) (synC1c))).fv ∪
        ((Class.cv (nb069AlphaDummy016 a b))).fv)
      0

theorem nb069_fresh_038 :
    (nb069AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb069AlphaDummy006)
              (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
                (Wff.classEq (Class.cv (nb069AlphaDummy006))
                  (synCphi (Class.cv (nb069AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb069AlphaDummy006)
              (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
                (Wff.classEq (Class.cv (nb069AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb069AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb069AlphaDummy006)
              (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
                (Wff.classEq (Class.cv (nb069AlphaDummy006))
                  (synCphi (Class.cv (nb069AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb069AlphaDummy006)
              (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
                (Wff.classEq (Class.cv (nb069AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb069_fresh_039 (a : Var) (b : Var) :
    (nb069AlphaDummy011 a b) ∉
      (((synCcompl (Class.cab (nb069AlphaDummy008 a b)
              (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                  (synCphi (Class.cv (nb069AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb069AlphaDummy008 a b)
              (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                  (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb069AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb069AlphaDummy008 a b)
              (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                  (synCphi (Class.cv (nb069AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb069AlphaDummy008 a b)
              (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                  (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb069_fresh_040 :
    (nb069AlphaDummy030) ∉
      (((synCcompl (Class.cv (nb069AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb069AlphaDummy022)))).fv) :=
  by
  simpa only [nb069AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb069AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb069AlphaDummy022)))).fv)
      0

theorem nb069_fresh_041 (a : Var) (b : Var) :
    (nb069AlphaDummy031 a b) ∉
      (((synCcompl (Class.cv (nb069AlphaDummy024 a b)))).fv ∪
        ((synCcompl (Class.cv (nb069AlphaDummy025 a b)))).fv) :=
  by
  simpa only [nb069AlphaDummy031] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb069AlphaDummy024 a b)))).fv ∪
        ((synCcompl (Class.cv (nb069AlphaDummy025 a b)))).fv)
      0

theorem nb069_fresh_042 :
    (nb069AlphaDummy038) ∉
      (((synCcompl (synCphi (Class.cv (nb069AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb069AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb069AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb069_fresh_043 (a : Var) (b : Var) :
    (nb069AlphaDummy039 a b) ∉
      (((synCcompl (synCphi (Class.cv (nb069AlphaDummy009 a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb069AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb069AlphaDummy009 a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb069_fresh_044 :
    (nb069AlphaDummy042) ∉
      (((synCnin (Class.cv (nb069AlphaDummy002)) (Class.cv (nb069AlphaDummy003)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy002))
            (Class.cv (nb069AlphaDummy003)))).fv) :=
  by
  simpa only [nb069AlphaDummy042] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb069AlphaDummy002)) (Class.cv (nb069AlphaDummy003)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy002)) (Class.cv (nb069AlphaDummy003)))).fv)
      0

theorem nb069_fresh_045 :
    (nb069AlphaDummy026) ∉
      (((synCnin (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy021))
            (Class.cv (nb069AlphaDummy022)))).fv) :=
  by
  simpa only [nb069AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022)))).fv)
      0

theorem nb069_fresh_046 (a : Var) (b : Var) :
    (nb069AlphaDummy027 a b) ∉
      (((synCnin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b)))).fv) :=
  by
  simpa only [nb069AlphaDummy027] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b)))).fv)
      0

theorem nb069_fresh_047 (x : Var) (y : Var) :
    (nb069AlphaDummy043 x y) ∉
      (((synCnin (Class.cv x) (Class.cv y))).fv ∪ ((synCnin (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb069AlphaDummy043] using
    freshVar_not_mem
      (((synCnin (Class.cv x) (Class.cv y))).fv ∪ ((synCnin (Class.cv x) (Class.cv y))).fv)
      0

theorem nb069_fresh_048 :
    (nb069AlphaDummy040) ∉
      (((synCphi (Class.cv (nb069AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb069AlphaDummy007)))).fv) :=
  by
  simpa only [nb069AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb069AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb069AlphaDummy007)))).fv)
      0

theorem nb069_fresh_049 (a : Var) (b : Var) :
    (nb069AlphaDummy041 a b) ∉
      (((synCphi (Class.cv (nb069AlphaDummy009 a b)))).fv ∪
        ((synCphi (Class.cv (nb069AlphaDummy009 a b)))).fv) :=
  by
  simpa only [nb069AlphaDummy041] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb069AlphaDummy009 a b)))).fv ∪
        ((synCphi (Class.cv (nb069AlphaDummy009 a b)))).fv)
      0

theorem nb069_fresh_050 :
    (nb069AlphaDummy004) ∉
      (({(nb069AlphaDummy000)} : Finset Var) ∪ ({(nb069AlphaDummy001)} : Finset Var) ∪
        ((synWrex (nb069AlphaDummy002) (Class.cv (nb069AlphaDummy000))
            (synWrex (nb069AlphaDummy003) (Class.cv (nb069AlphaDummy001))
              (synWss (Class.cv (nb069AlphaDummy002))
                (Class.cv (nb069AlphaDummy003)))))).fv) :=
  by
  simpa only [nb069AlphaDummy004] using
    freshVar_not_mem
      (({(nb069AlphaDummy000)} : Finset Var) ∪ ({(nb069AlphaDummy001)} : Finset Var) ∪
        ((synWrex (nb069AlphaDummy002) (Class.cv (nb069AlphaDummy000))
            (synWrex (nb069AlphaDummy003) (Class.cv (nb069AlphaDummy001))
              (synWss (Class.cv (nb069AlphaDummy002))
                (Class.cv (nb069AlphaDummy003)))))).fv)
      0

theorem nb069_fresh_051 (x : Var) (y : Var) (a : Var) (b : Var) :
    (nb069AlphaDummy005 x y a b) ∉
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWss (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb069AlphaDummy005] using
    freshVar_not_mem
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWss (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb069_fresh_052 : (nb069AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb069AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb069_fresh_053 : (nb069AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb069AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb069_fresh_054 : (nb069AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb069AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb069_fresh_055 : (nb069AlphaDummy003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb069AlphaDummy003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb069_distinct_056 : (nb069AlphaDummy000) ≠ (nb069AlphaDummy001) := by
  simpa only [nb069AlphaDummy000, nb069AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb069_distinct_057 : (nb069AlphaDummy000) ≠ (nb069AlphaDummy002) := by
  simpa only [nb069AlphaDummy000, nb069AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb069_distinct_058 : (nb069AlphaDummy000) ≠ (nb069AlphaDummy003) := by
  simpa only [nb069AlphaDummy000, nb069AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb069_distinct_059 : (nb069AlphaDummy001) ≠ (nb069AlphaDummy002) := by
  simpa only [nb069AlphaDummy001, nb069AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb069_distinct_060 : (nb069AlphaDummy001) ≠ (nb069AlphaDummy003) := by
  simpa only [nb069AlphaDummy001, nb069AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb069_distinct_061 : (nb069AlphaDummy002) ≠ (nb069AlphaDummy003) := by
  simpa only [nb069AlphaDummy002, nb069AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb069_support_mem_0000 :
    (nb069AlphaDummy000) ∈
      (({(nb069AlphaDummy000)} : Finset Var) ∪ ({(nb069AlphaDummy001)} : Finset Var) ∪
        ((synWrex (nb069AlphaDummy002) (Class.cv (nb069AlphaDummy000))
            (synWrex (nb069AlphaDummy003) (Class.cv (nb069AlphaDummy001))
              (synWss (Class.cv (nb069AlphaDummy002))
                (Class.cv (nb069AlphaDummy003)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0001 (x : Var) (y : Var) (a : Var) (b : Var) :
    a ∈
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWss (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0002 :
    (nb069AlphaDummy001) ∈
      (({(nb069AlphaDummy000)} : Finset Var) ∪ ({(nb069AlphaDummy001)} : Finset Var) ∪
        ((synWrex (nb069AlphaDummy002) (Class.cv (nb069AlphaDummy000))
            (synWrex (nb069AlphaDummy003) (Class.cv (nb069AlphaDummy001))
              (synWss (Class.cv (nb069AlphaDummy002))
                (Class.cv (nb069AlphaDummy003)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0003 (x : Var) (y : Var) (a : Var) (b : Var) :
    b ∈
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWss (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0004 :
    (nb069AlphaDummy000) ∈
      (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0005 :
    (nb069AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb069AlphaDummy006)
              (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
                (Wff.classEq (Class.cv (nb069AlphaDummy006))
                  (synCphi (Class.cv (nb069AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb069AlphaDummy006)
              (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
                (Wff.classEq (Class.cv (nb069AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy006) from (by
          unfold nb069AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy007) from (by
            unfold nb069AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0006 (a : Var) (b : Var) :
    a ∈ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0007 (a : Var) (b : Var) :
    a ∈
      (((synCcompl (Class.cab (nb069AlphaDummy008 a b)
              (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                  (synCphi (Class.cv (nb069AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb069AlphaDummy008 a b)
              (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                  (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb069AlphaDummy008 a b) from (by
          unfold nb069AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb069AlphaDummy009 a b) from (by
            unfold nb069AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0008 :
    (nb069AlphaDummy000) ∈
      (((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCphi (Class.cv (nb069AlphaDummy007))))))).fv ∪
        ((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCphi (Class.cv (nb069AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy006) from (by
          unfold nb069AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy007) from (by
            unfold nb069AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0009 (a : Var) (b : Var) :
    a ∈
      (((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCphi (Class.cv (nb069AlphaDummy009 a b))))))).fv ∪
        ((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCphi (Class.cv (nb069AlphaDummy009 a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb069AlphaDummy008 a b) from (by
          unfold nb069AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb069AlphaDummy009 a b) from (by
            unfold nb069AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0010 :
    (nb069AlphaDummy007) ∈ (((Class.cv (nb069AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0011 (a : Var) (b : Var) :
    (nb069AlphaDummy009 a b) ∈ (((Class.cv (nb069AlphaDummy009 a b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0012 :
    (nb069AlphaDummy014) ∈
      (((Wff.classMem (Class.cv (nb069AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb069AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb069AlphaDummy014))).fv) :=
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

theorem nb069_support_mem_0013 (a : Var) (b : Var) :
    (nb069AlphaDummy016 a b) ∈
      (((Wff.classMem (Class.cv (nb069AlphaDummy016 a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb069AlphaDummy016 a b)) (synC1c))).fv ∪
        ((Class.cv (nb069AlphaDummy016 a b))).fv) :=
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

theorem nb069_support_mem_0014 :
    (nb069AlphaDummy014) ∈
      (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0015 (a : Var) (b : Var) :
    (nb069AlphaDummy016 a b) ∈
      (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0016 :
    (nb069AlphaDummy021) ∈
      (((synCnin (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy021))
            (Class.cv (nb069AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0017 (a : Var) (b : Var) :
    (nb069AlphaDummy024 a b) ∈
      (((synCnin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0018 :
    (nb069AlphaDummy021) ∈
      (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0019 (a : Var) (b : Var) :
    (nb069AlphaDummy024 a b) ∈
      (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0020 :
    (nb069AlphaDummy022) ∈
      (((synCnin (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy021))
            (Class.cv (nb069AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0021 (a : Var) (b : Var) :
    (nb069AlphaDummy025 a b) ∈
      (((synCnin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b)))).fv ∪
        ((synCnin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0022 :
    (nb069AlphaDummy022) ∈
      (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0023 (a : Var) (b : Var) :
    (nb069AlphaDummy025 a b) ∈
      (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0024 :
    (nb069AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb069AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb069AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0025 (a : Var) (b : Var) :
    (nb069AlphaDummy024 a b) ∈
      (((synCcompl (Class.cv (nb069AlphaDummy024 a b)))).fv ∪
        ((synCcompl (Class.cv (nb069AlphaDummy025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0026 :
    (nb069AlphaDummy021) ∈
      (((Class.cv (nb069AlphaDummy021))).fv ∪ ((Class.cv (nb069AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0027 (a : Var) (b : Var) :
    (nb069AlphaDummy024 a b) ∈
      (((Class.cv (nb069AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy024 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0028 :
    (nb069AlphaDummy022) ∈
      (((synCcompl (Class.cv (nb069AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb069AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0029 (a : Var) (b : Var) :
    (nb069AlphaDummy025 a b) ∈
      (((synCcompl (Class.cv (nb069AlphaDummy024 a b)))).fv ∪
        ((synCcompl (Class.cv (nb069AlphaDummy025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0030 :
    (nb069AlphaDummy022) ∈
      (((Class.cv (nb069AlphaDummy022))).fv ∪ ((Class.cv (nb069AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0031 (a : Var) (b : Var) :
    (nb069AlphaDummy025 a b) ∈
      (((Class.cv (nb069AlphaDummy025 a b))).fv ∪
        ((Class.cv (nb069AlphaDummy025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0032 :
    (nb069AlphaDummy001) ∈
      (((Class.cv (nb069AlphaDummy000))).fv ∪ ((Class.cv (nb069AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0033 :
    (nb069AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb069AlphaDummy006)
              (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy000))
                (Wff.classEq (Class.cv (nb069AlphaDummy006))
                  (synCphi (Class.cv (nb069AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb069AlphaDummy006)
              (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
                (Wff.classEq (Class.cv (nb069AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy006) from (by
          unfold nb069AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy007) from (by
            unfold nb069AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0034 (a : Var) (b : Var) :
    b ∈ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0035 (a : Var) (b : Var) :
    b ∈
      (((synCcompl (Class.cab (nb069AlphaDummy008 a b)
              (synWrex (nb069AlphaDummy009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                  (synCphi (Class.cv (nb069AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb069AlphaDummy008 a b)
              (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                  (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb069AlphaDummy008 a b) from (by
          unfold nb069AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0034 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb069AlphaDummy009 a b) from (by
            unfold nb069AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0034 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0036 :
    (nb069AlphaDummy001) ∈
      (((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb069AlphaDummy006)
            (synWrex (nb069AlphaDummy007) (Class.cv (nb069AlphaDummy001))
              (Wff.classEq (Class.cv (nb069AlphaDummy006))
                (synCun (synCphi (Class.cv (nb069AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy006) from (by
          unfold nb069AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy007) from (by
            unfold nb069AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0037 (a : Var) (b : Var) :
    b ∈
      (((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb069AlphaDummy008 a b)
            (synWrex (nb069AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb069AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb069AlphaDummy008 a b) from (by
          unfold nb069AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0034 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb069AlphaDummy009 a b) from (by
            unfold nb069AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0034 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb069_support_mem_0038 :
    (nb069AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb069AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0039 (a : Var) (b : Var) :
    (nb069AlphaDummy009 a b) ∈
      (((synCcompl (synCphi (Class.cv (nb069AlphaDummy009 a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0040 :
    (nb069AlphaDummy007) ∈
      (((synCphi (Class.cv (nb069AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb069AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0041 (a : Var) (b : Var) :
    (nb069AlphaDummy009 a b) ∈
      (((synCphi (Class.cv (nb069AlphaDummy009 a b)))).fv ∪
        ((synCphi (Class.cv (nb069AlphaDummy009 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
