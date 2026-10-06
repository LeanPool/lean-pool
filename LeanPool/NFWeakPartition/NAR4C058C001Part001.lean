/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C058C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_000`. -/
@[expose]
noncomputable def nb058AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_001`. -/
@[expose]
noncomputable def nb058AlphaDummy001 : Var :=
  (freshVar (({(nb058AlphaDummy000)} : Finset Var) ∪ ((synC1c)).fv ∪
      ((synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_002`. -/
@[expose]
noncomputable def nb058AlphaDummy002 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synC1c)).fv ∪ ((synCpw1 (synCuni (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_003`. -/
@[expose]
noncomputable def nb058AlphaDummy003 : Var :=
  (freshVar
    (({(nb058AlphaDummy000)} : Finset Var) ∪ ({(nb058AlphaDummy001)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb058AlphaDummy000)) (synC1c))
          (Wff.classEq (Class.cv (nb058AlphaDummy001))
            (synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_004`. -/
@[expose]
noncomputable def nb058AlphaDummy004 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb058AlphaDummy002 x)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv x) (synC1c))
          (Wff.classEq (Class.cv (nb058AlphaDummy002 x))
            (synCpw1 (synCuni (Class.cv x)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_005`. -/
@[expose]
noncomputable def nb058AlphaDummy005 : Var :=
  (freshVar
    (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_006`. -/
@[expose]
noncomputable def nb058AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_007`. -/
@[expose]
noncomputable def nb058AlphaDummy007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_008`. -/
@[expose]
noncomputable def nb058AlphaDummy008 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_009`. -/
@[expose]
noncomputable def nb058AlphaDummy009 : Var :=
  (freshVar (((synCcompl (Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCphi (Class.cv (nb058AlphaDummy006)))))))).fv ∪ ((synCcompl
          (Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_010`. -/
@[expose]
noncomputable def nb058AlphaDummy010 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb058AlphaDummy007 x)
            (synWrex (nb058AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCphi (Class.cv (nb058AlphaDummy008 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb058AlphaDummy007 x)
            (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_011`. -/
@[expose]
noncomputable def nb058AlphaDummy011 : Var :=
  (freshVar (((Class.cab (nb058AlphaDummy005)
          (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
            (Wff.classEq (Class.cv (nb058AlphaDummy005))
              (synCphi (Class.cv (nb058AlphaDummy006))))))).fv ∪
      ((Class.cab (nb058AlphaDummy005)
          (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
            (Wff.classEq (Class.cv (nb058AlphaDummy005))
              (synCphi (Class.cv (nb058AlphaDummy006))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_012`. -/
@[expose]
noncomputable def nb058AlphaDummy012 (x : Var) : Var :=
  (freshVar (((Class.cab (nb058AlphaDummy007 x)
          (synWrex (nb058AlphaDummy008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
              (synCphi (Class.cv (nb058AlphaDummy008 x))))))).fv ∪
      ((Class.cab (nb058AlphaDummy007 x) (synWrex (nb058AlphaDummy008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
              (synCphi (Class.cv (nb058AlphaDummy008 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_013`. -/
@[expose]
noncomputable def nb058AlphaDummy013 : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_014`. -/
@[expose]
noncomputable def nb058AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy006))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_015`. -/
@[expose]
noncomputable def nb058AlphaDummy015 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy008 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_016`. -/
@[expose]
noncomputable def nb058AlphaDummy016 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy008 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_017`. -/
@[expose]
noncomputable def nb058AlphaDummy017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb058AlphaDummy013)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb058AlphaDummy013)) (synC1c))).fv ∪
      ((Class.cv (nb058AlphaDummy013))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_018`. -/
@[expose]
noncomputable def nb058AlphaDummy018 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb058AlphaDummy015 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb058AlphaDummy015 x)) (synC1c))).fv ∪
      ((Class.cv (nb058AlphaDummy015 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_019`. -/
@[expose]
noncomputable def nb058AlphaDummy019 : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_020`. -/
@[expose]
noncomputable def nb058AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_021`. -/
@[expose]
noncomputable def nb058AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_022`. -/
@[expose]
noncomputable def nb058AlphaDummy022 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_023`. -/
@[expose]
noncomputable def nb058AlphaDummy023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_024`. -/
@[expose]
noncomputable def nb058AlphaDummy024 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_025`. -/
@[expose]
noncomputable def nb058AlphaDummy025 : Var :=
  (freshVar (((synCnin (Class.cv (nb058AlphaDummy020))
          (Class.cv (nb058AlphaDummy021)))).fv ∪
      ((synCnin (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_026`. -/
@[expose]
noncomputable def nb058AlphaDummy026 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb058AlphaDummy023 x))
          (Class.cv (nb058AlphaDummy024 x)))).fv ∪
      ((synCnin (Class.cv (nb058AlphaDummy023 x)) (Class.cv (nb058AlphaDummy024 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_027`. -/
@[expose]
noncomputable def nb058AlphaDummy027 : Var :=
  (freshVar
    (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_028`. -/
@[expose]
noncomputable def nb058AlphaDummy028 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy023 x))).fv ∪
      ((Class.cv (nb058AlphaDummy024 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_029`. -/
@[expose]
noncomputable def nb058AlphaDummy029 : Var :=
  (freshVar (((synCcompl (Class.cv (nb058AlphaDummy020)))).fv ∪
      ((synCcompl (Class.cv (nb058AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_030`. -/
@[expose]
noncomputable def nb058AlphaDummy030 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb058AlphaDummy023 x)))).fv ∪
      ((synCcompl (Class.cv (nb058AlphaDummy024 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_031`. -/
@[expose]
noncomputable def nb058AlphaDummy031 : Var :=
  (freshVar
    (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_032`. -/
@[expose]
noncomputable def nb058AlphaDummy032 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy023 x))).fv ∪
      ((Class.cv (nb058AlphaDummy023 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_033`. -/
@[expose]
noncomputable def nb058AlphaDummy033 : Var :=
  (freshVar
    (((Class.cv (nb058AlphaDummy021))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_034`. -/
@[expose]
noncomputable def nb058AlphaDummy034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy024 x))).fv ∪
      ((Class.cv (nb058AlphaDummy024 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_035`. -/
@[expose]
noncomputable def nb058AlphaDummy035 : Var :=
  (freshVar (((Class.cab (nb058AlphaDummy005)
          (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
            (Wff.classEq (Class.cv (nb058AlphaDummy005))
              (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb058AlphaDummy005)
          (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
            (Wff.classEq (Class.cv (nb058AlphaDummy005))
              (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_036`. -/
@[expose]
noncomputable def nb058AlphaDummy036 (x : Var) : Var :=
  (freshVar (((Class.cab (nb058AlphaDummy007 x)
          (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
            (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
              (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb058AlphaDummy007 x)
          (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
            (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
              (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_037`. -/
@[expose]
noncomputable def nb058AlphaDummy037 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb058AlphaDummy006))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_038`. -/
@[expose]
noncomputable def nb058AlphaDummy038 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb058AlphaDummy008 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_039`. -/
@[expose]
noncomputable def nb058AlphaDummy039 : Var :=
  (freshVar (((synCphi (Class.cv (nb058AlphaDummy006)))).fv ∪
      ((synCphi (Class.cv (nb058AlphaDummy006)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_040`. -/
@[expose]
noncomputable def nb058AlphaDummy040 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb058AlphaDummy008 x)))).fv ∪
      ((synCphi (Class.cv (nb058AlphaDummy008 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_041`. -/
@[expose]
noncomputable def nb058AlphaDummy041 : Var :=
  (freshVar (((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv ∪
      ((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_042`. -/
@[expose]
noncomputable def nb058AlphaDummy042 (x : Var) : Var :=
  (freshVar (((synCnin (synCpw (synCuni (Class.cv x))) (synC1c))).fv ∪
      ((synCnin (synCpw (synCuni (Class.cv x))) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_043`. -/
@[expose]
noncomputable def nb058AlphaDummy043 : Var :=
  (freshVar (((synCpw (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_044`. -/
@[expose]
noncomputable def nb058AlphaDummy044 (x : Var) : Var :=
  (freshVar (((synCpw (synCuni (Class.cv x)))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_045`. -/
@[expose]
noncomputable def nb058AlphaDummy045 : Var :=
  (freshVar (((synCuni (Class.cv (nb058AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_046`. -/
@[expose]
noncomputable def nb058AlphaDummy046 (x : Var) : Var :=
  (freshVar (((synCuni (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_047`. -/
@[expose]
noncomputable def nb058AlphaDummy047 : Var :=
  (freshVar (((synCnin (Class.cv (nb058AlphaDummy045))
          (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪
      ((synCnin (Class.cv (nb058AlphaDummy045))
          (synCuni (Class.cv (nb058AlphaDummy000))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_048`. -/
@[expose]
noncomputable def nb058AlphaDummy048 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv ∪
      ((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_049`. -/
@[expose]
noncomputable def nb058AlphaDummy049 : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy045))).fv ∪
      ((synCuni (Class.cv (nb058AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_050`. -/
@[expose]
noncomputable def nb058AlphaDummy050 (x : Var) : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy046 x))).fv ∪ ((synCuni (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_051`. -/
@[expose]
noncomputable def nb058AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_052`. -/
@[expose]
noncomputable def nb058AlphaDummy052 : Var :=
  (freshVar (((Class.cv (nb058AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_053`. -/
@[expose]
noncomputable def nb058AlphaDummy053 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_054`. -/
@[expose]
noncomputable def nb058AlphaDummy054 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 1)

theorem nb058_fresh_000 :
    (nb058AlphaDummy011) ∉
      (((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCphi (Class.cv (nb058AlphaDummy006))))))).fv ∪
        ((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCphi (Class.cv (nb058AlphaDummy006))))))).fv) :=
  by
  simpa only [nb058AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCphi (Class.cv (nb058AlphaDummy006))))))).fv ∪
        ((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCphi (Class.cv (nb058AlphaDummy006))))))).fv)
      0

theorem nb058_fresh_001 :
    (nb058AlphaDummy035) ∉
      (((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb058AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb058_fresh_002 (x : Var) :
    (nb058AlphaDummy036 x) ∉
      (((Class.cab (nb058AlphaDummy007 x)
            (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb058AlphaDummy007 x)
            (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb058AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb058AlphaDummy007 x)
            (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb058AlphaDummy007 x)
            (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb058_fresh_003 (x : Var) :
    (nb058AlphaDummy012 x) ∉
      (((Class.cab (nb058AlphaDummy007 x) (synWrex (nb058AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCphi (Class.cv (nb058AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb058AlphaDummy007 x) (synWrex (nb058AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCphi (Class.cv (nb058AlphaDummy008 x))))))).fv) :=
  by
  simpa only [nb058AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb058AlphaDummy007 x) (synWrex (nb058AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCphi (Class.cv (nb058AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb058AlphaDummy007 x) (synWrex (nb058AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCphi (Class.cv (nb058AlphaDummy008 x))))))).fv)
      0

theorem nb058_fresh_004 :
    (nb058AlphaDummy051) ∉ (((Class.cv (nb058AlphaDummy000))).fv) := by
  simpa only [nb058AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy000))).fv) 0

theorem nb058_fresh_005 :
    (nb058AlphaDummy052) ∉ (((Class.cv (nb058AlphaDummy000))).fv) := by
  simpa only [nb058AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy000))).fv) 1

theorem nb058_distinct_006 : (nb058AlphaDummy051) ≠ (nb058AlphaDummy052) := by
  simpa only [nb058AlphaDummy051, nb058AlphaDummy052] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy000))).fv) (i := 0) (j := 1) (by decide))

theorem nb058_fresh_007 :
    (nb058AlphaDummy005) ∉
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv) :=
  by
  simpa only [nb058AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv)
      0

theorem nb058_fresh_008 :
    (nb058AlphaDummy006) ∉
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv) :=
  by
  simpa only [nb058AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv)
      1

theorem nb058_distinct_009 : (nb058AlphaDummy005) ≠ (nb058AlphaDummy006) := by
  simpa only [nb058AlphaDummy005, nb058AlphaDummy006] using
    (freshVar_injective
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb058_fresh_010 :
    (nb058AlphaDummy013) ∉ (((Class.cv (nb058AlphaDummy006))).fv) := by
  simpa only [nb058AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy006))).fv) 0

theorem nb058_fresh_011 :
    (nb058AlphaDummy014) ∉ (((Class.cv (nb058AlphaDummy006))).fv) := by
  simpa only [nb058AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy006))).fv) 1

theorem nb058_distinct_012 : (nb058AlphaDummy013) ≠ (nb058AlphaDummy014) := by
  simpa only [nb058AlphaDummy013, nb058AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy006))).fv) (i := 0) (j := 1) (by decide))

theorem nb058_fresh_013 (x : Var) :
    (nb058AlphaDummy015 x) ∉ (((Class.cv (nb058AlphaDummy008 x))).fv) := by
  simpa only [nb058AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy008 x))).fv) 0

theorem nb058_fresh_014 (x : Var) :
    (nb058AlphaDummy016 x) ∉ (((Class.cv (nb058AlphaDummy008 x))).fv) := by
  simpa only [nb058AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy008 x))).fv) 1

theorem nb058_distinct_015 (x : Var) :
    (nb058AlphaDummy015 x) ≠ (nb058AlphaDummy016 x) := by
  simpa only [nb058AlphaDummy015, nb058AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy008 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb058_fresh_016 :
    (nb058AlphaDummy019) ∉
      (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb058AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) 0

theorem nb058_fresh_017 :
    (nb058AlphaDummy020) ∉
      (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb058AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) 1

theorem nb058_fresh_018 :
    (nb058AlphaDummy021) ∉
      (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb058AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) 2

theorem nb058_distinct_019 : (nb058AlphaDummy019) ≠ (nb058AlphaDummy020) := by
  simpa only [nb058AlphaDummy019, nb058AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb058_distinct_020 : (nb058AlphaDummy019) ≠ (nb058AlphaDummy021) := by
  simpa only [nb058AlphaDummy019, nb058AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb058_distinct_021 : (nb058AlphaDummy020) ≠ (nb058AlphaDummy021) := by
  simpa only [nb058AlphaDummy020, nb058AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb058_fresh_022 (x : Var) :
    (nb058AlphaDummy022 x) ∉
      (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb058AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 0

theorem nb058_fresh_023 (x : Var) :
    (nb058AlphaDummy023 x) ∉
      (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb058AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 1

theorem nb058_fresh_024 (x : Var) :
    (nb058AlphaDummy024 x) ∉
      (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb058AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 2

theorem nb058_distinct_025 (x : Var) :
    (nb058AlphaDummy022 x) ≠ (nb058AlphaDummy023 x) := by
  simpa only [nb058AlphaDummy022, nb058AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb058_distinct_026 (x : Var) :
    (nb058AlphaDummy022 x) ≠ (nb058AlphaDummy024 x) := by
  simpa only [nb058AlphaDummy022, nb058AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb058_distinct_027 (x : Var) :
    (nb058AlphaDummy023 x) ≠ (nb058AlphaDummy024 x) := by
  simpa only [nb058AlphaDummy023, nb058AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb058_fresh_028 :
    (nb058AlphaDummy031) ∉
      (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy020))).fv) :=
  by
  simpa only [nb058AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy020))).fv)
      0

theorem nb058_fresh_029 :
    (nb058AlphaDummy027) ∉
      (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv) :=
  by
  simpa only [nb058AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv)
      0

theorem nb058_fresh_030 :
    (nb058AlphaDummy033) ∉
      (((Class.cv (nb058AlphaDummy021))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv) :=
  by
  simpa only [nb058AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy021))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv)
      0

theorem nb058_fresh_031 (x : Var) :
    (nb058AlphaDummy032 x) ∉
      (((Class.cv (nb058AlphaDummy023 x))).fv ∪ ((Class.cv (nb058AlphaDummy023 x))).fv) :=
  by
  simpa only [nb058AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy023 x))).fv ∪ ((Class.cv (nb058AlphaDummy023 x))).fv)
      0

theorem nb058_fresh_032 (x : Var) :
    (nb058AlphaDummy028 x) ∉
      (((Class.cv (nb058AlphaDummy023 x))).fv ∪ ((Class.cv (nb058AlphaDummy024 x))).fv) :=
  by
  simpa only [nb058AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy023 x))).fv ∪ ((Class.cv (nb058AlphaDummy024 x))).fv)
      0

theorem nb058_fresh_033 (x : Var) :
    (nb058AlphaDummy034 x) ∉
      (((Class.cv (nb058AlphaDummy024 x))).fv ∪ ((Class.cv (nb058AlphaDummy024 x))).fv) :=
  by
  simpa only [nb058AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy024 x))).fv ∪ ((Class.cv (nb058AlphaDummy024 x))).fv)
      0

theorem nb058_fresh_034 :
    (nb058AlphaDummy049) ∉
      (((Class.cv (nb058AlphaDummy045))).fv ∪
        ((synCuni (Class.cv (nb058AlphaDummy000)))).fv) :=
  by
  simpa only [nb058AlphaDummy049] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy045))).fv ∪
        ((synCuni (Class.cv (nb058AlphaDummy000)))).fv)
      0

theorem nb058_fresh_035 (x : Var) :
    (nb058AlphaDummy050 x) ∉
      (((Class.cv (nb058AlphaDummy046 x))).fv ∪ ((synCuni (Class.cv x))).fv) :=
  by
  simpa only [nb058AlphaDummy050] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy046 x))).fv ∪ ((synCuni (Class.cv x))).fv) 0

theorem nb058_fresh_036 (x : Var) : (nb058AlphaDummy053 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb058AlphaDummy053] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb058_fresh_037 (x : Var) : (nb058AlphaDummy054 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb058AlphaDummy054] using freshVar_not_mem (((Class.cv x)).fv) 1

theorem nb058_distinct_038 (x : Var) :
    (nb058AlphaDummy053 x) ≠ (nb058AlphaDummy054 x) := by
  simpa only [nb058AlphaDummy053, nb058AlphaDummy054] using
    (freshVar_injective (((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb058_fresh_039 (x : Var) :
    (nb058AlphaDummy007 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) :=
  by
  simpa only [nb058AlphaDummy007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) 0

theorem nb058_fresh_040 (x : Var) :
    (nb058AlphaDummy008 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) :=
  by
  simpa only [nb058AlphaDummy008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) 1

theorem nb058_distinct_041 (x : Var) :
    (nb058AlphaDummy007 x) ≠ (nb058AlphaDummy008 x) := by
  simpa only [nb058AlphaDummy007, nb058AlphaDummy008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb058_fresh_042 :
    (nb058AlphaDummy017) ∉
      (((Wff.classMem (Class.cv (nb058AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb058AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb058AlphaDummy013))).fv) :=
  by
  simpa only [nb058AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb058AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb058AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb058AlphaDummy013))).fv)
      0

theorem nb058_fresh_043 (x : Var) :
    (nb058AlphaDummy018 x) ∉
      (((Wff.classMem (Class.cv (nb058AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb058AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb058AlphaDummy015 x))).fv) :=
  by
  simpa only [nb058AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb058AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb058AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb058AlphaDummy015 x))).fv)
      0

theorem nb058_fresh_044 :
    (nb058AlphaDummy009) ∉
      (((synCcompl (Class.cab (nb058AlphaDummy005)
              (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
                (Wff.classEq (Class.cv (nb058AlphaDummy005))
                  (synCphi (Class.cv (nb058AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb058AlphaDummy005)
              (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
                (Wff.classEq (Class.cv (nb058AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb058AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb058AlphaDummy005)
              (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
                (Wff.classEq (Class.cv (nb058AlphaDummy005))
                  (synCphi (Class.cv (nb058AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb058AlphaDummy005)
              (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
                (Wff.classEq (Class.cv (nb058AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb058_fresh_045 (x : Var) :
    (nb058AlphaDummy010 x) ∉
      (((synCcompl (Class.cab (nb058AlphaDummy007 x)
              (synWrex (nb058AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                  (synCphi (Class.cv (nb058AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb058AlphaDummy007 x)
              (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb058AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb058AlphaDummy007 x)
              (synWrex (nb058AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                  (synCphi (Class.cv (nb058AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb058AlphaDummy007 x)
              (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb058_fresh_046 :
    (nb058AlphaDummy029) ∉
      (((synCcompl (Class.cv (nb058AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb058AlphaDummy021)))).fv) :=
  by
  simpa only [nb058AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb058AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb058AlphaDummy021)))).fv)
      0

theorem nb058_fresh_047 (x : Var) :
    (nb058AlphaDummy030 x) ∉
      (((synCcompl (Class.cv (nb058AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb058AlphaDummy024 x)))).fv) :=
  by
  simpa only [nb058AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb058AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb058AlphaDummy024 x)))).fv)
      0

theorem nb058_fresh_048 :
    (nb058AlphaDummy037) ∉
      (((synCcompl (synCphi (Class.cv (nb058AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb058AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb058AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb058_fresh_049 (x : Var) :
    (nb058AlphaDummy038 x) ∉
      (((synCcompl (synCphi (Class.cv (nb058AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb058AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb058AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb058_fresh_050 :
    (nb058AlphaDummy025) ∉
      (((synCnin (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy020))
            (Class.cv (nb058AlphaDummy021)))).fv) :=
  by
  simpa only [nb058AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021)))).fv)
      0

theorem nb058_fresh_051 (x : Var) :
    (nb058AlphaDummy026 x) ∉
      (((synCnin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x)))).fv) :=
  by
  simpa only [nb058AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x)))).fv)
      0

theorem nb058_fresh_052 :
    (nb058AlphaDummy047) ∉
      (((synCnin (Class.cv (nb058AlphaDummy045))
            (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy045))
            (synCuni (Class.cv (nb058AlphaDummy000))))).fv) :=
  by
  simpa only [nb058AlphaDummy047] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb058AlphaDummy045))
            (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy045))
            (synCuni (Class.cv (nb058AlphaDummy000))))).fv)
      0

theorem nb058_fresh_053 (x : Var) :
    (nb058AlphaDummy048 x) ∉
      (((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv) :=
  by
  simpa only [nb058AlphaDummy048] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv)
      0

theorem nb058_fresh_054 :
    (nb058AlphaDummy041) ∉
      (((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv ∪
        ((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv) :=
  by
  simpa only [nb058AlphaDummy041] using
    freshVar_not_mem
      (((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv ∪
        ((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv)
      0

theorem nb058_fresh_055 (x : Var) :
    (nb058AlphaDummy042 x) ∉
      (((synCnin (synCpw (synCuni (Class.cv x))) (synC1c))).fv ∪
        ((synCnin (synCpw (synCuni (Class.cv x))) (synC1c))).fv) :=
  by
  simpa only [nb058AlphaDummy042] using
    freshVar_not_mem
      (((synCnin (synCpw (synCuni (Class.cv x))) (synC1c))).fv ∪
        ((synCnin (synCpw (synCuni (Class.cv x))) (synC1c))).fv)
      0

theorem nb058_fresh_056 :
    (nb058AlphaDummy039) ∉
      (((synCphi (Class.cv (nb058AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb058AlphaDummy006)))).fv) :=
  by
  simpa only [nb058AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb058AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb058AlphaDummy006)))).fv)
      0

theorem nb058_fresh_057 (x : Var) :
    (nb058AlphaDummy040 x) ∉
      (((synCphi (Class.cv (nb058AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb058AlphaDummy008 x)))).fv) :=
  by
  simpa only [nb058AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb058AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb058AlphaDummy008 x)))).fv)
      0

theorem nb058_fresh_058 :
    (nb058AlphaDummy043) ∉
      (((synCpw (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb058AlphaDummy043] using
    freshVar_not_mem
      (((synCpw (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪ ((synC1c)).fv) 0

theorem nb058_fresh_059 (x : Var) :
    (nb058AlphaDummy044 x) ∉
      (((synCpw (synCuni (Class.cv x)))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb058AlphaDummy044] using
    freshVar_not_mem (((synCpw (synCuni (Class.cv x)))).fv ∪ ((synC1c)).fv) 0

theorem nb058_fresh_060 :
    (nb058AlphaDummy045) ∉ (((synCuni (Class.cv (nb058AlphaDummy000)))).fv) := by
  simpa only [nb058AlphaDummy045] using
    freshVar_not_mem (((synCuni (Class.cv (nb058AlphaDummy000)))).fv) 0

theorem nb058_fresh_061 (x : Var) :
    (nb058AlphaDummy046 x) ∉ (((synCuni (Class.cv x))).fv) := by
  simpa only [nb058AlphaDummy046] using
    freshVar_not_mem (((synCuni (Class.cv x))).fv) 0

theorem nb058_fresh_062 :
    (nb058AlphaDummy001) ∉
      (({(nb058AlphaDummy000)} : Finset Var) ∪ ((synC1c)).fv ∪
        ((synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))).fv) :=
  by
  simpa only [nb058AlphaDummy001] using
    freshVar_not_mem
      (({(nb058AlphaDummy000)} : Finset Var) ∪ ((synC1c)).fv ∪
        ((synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))).fv)
      0

theorem nb058_fresh_063 :
    (nb058AlphaDummy003) ∉
      (({(nb058AlphaDummy000)} : Finset Var) ∪ ({(nb058AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb058AlphaDummy000)) (synC1c))
            (Wff.classEq (Class.cv (nb058AlphaDummy001))
              (synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))))).fv) :=
  by
  simpa only [nb058AlphaDummy003] using
    freshVar_not_mem
      (({(nb058AlphaDummy000)} : Finset Var) ∪ ({(nb058AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb058AlphaDummy000)) (synC1c))
            (Wff.classEq (Class.cv (nb058AlphaDummy001))
              (synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))))).fv)
      0

theorem nb058_fresh_064 (x : Var) :
    (nb058AlphaDummy002 x) ∉
      (({ x } : Finset Var) ∪ ((synC1c)).fv ∪ ((synCpw1 (synCuni (Class.cv x)))).fv) :=
  by
  simpa only [nb058AlphaDummy002] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synC1c)).fv ∪ ((synCpw1 (synCuni (Class.cv x)))).fv) 0

theorem nb058_fresh_065 (x : Var) :
    (nb058AlphaDummy004 x) ∉
      (({ x } : Finset Var) ∪ ({(nb058AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synC1c))
            (Wff.classEq (Class.cv (nb058AlphaDummy002 x))
              (synCpw1 (synCuni (Class.cv x)))))).fv) :=
  by
  simpa only [nb058AlphaDummy004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb058AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synC1c))
            (Wff.classEq (Class.cv (nb058AlphaDummy002 x))
              (synCpw1 (synCuni (Class.cv x)))))).fv)
      0

theorem nb058_fresh_066 : (nb058AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb058AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb058_support_mem_0000 :
    (nb058AlphaDummy000) ∈
      (({(nb058AlphaDummy000)} : Finset Var) ∪ ({(nb058AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb058AlphaDummy000)) (synC1c))
            (Wff.classEq (Class.cv (nb058AlphaDummy001))
              (synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0001 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb058AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synC1c))
            (Wff.classEq (Class.cv (nb058AlphaDummy002 x))
              (synCpw1 (synCuni (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0002 :
    (nb058AlphaDummy001) ∈
      (({(nb058AlphaDummy000)} : Finset Var) ∪ ({(nb058AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb058AlphaDummy000)) (synC1c))
            (Wff.classEq (Class.cv (nb058AlphaDummy001))
              (synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0003 (x : Var) :
    (nb058AlphaDummy002 x) ∈
      (({ x } : Finset Var) ∪ ({(nb058AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synC1c))
            (Wff.classEq (Class.cv (nb058AlphaDummy002 x))
              (synCpw1 (synCuni (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0004 :
    (nb058AlphaDummy000) ∈
      (({(nb058AlphaDummy000)} : Finset Var) ∪ ((synC1c)).fv ∪
        ((synCpw1 (synCuni (Class.cv (nb058AlphaDummy000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0005 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synC1c)).fv ∪ ((synCpw1 (synCuni (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0006 :
    (nb058AlphaDummy000) ∈
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0007 :
    (nb058AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb058AlphaDummy005)
              (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
                (Wff.classEq (Class.cv (nb058AlphaDummy005))
                  (synCphi (Class.cv (nb058AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb058AlphaDummy005)
              (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
                (Wff.classEq (Class.cv (nb058AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0008 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0009 (x : Var) :
    x ∈
      (((synCcompl (Class.cab (nb058AlphaDummy007 x)
              (synWrex (nb058AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                  (synCphi (Class.cv (nb058AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb058AlphaDummy007 x)
              (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0010 :
    (nb058AlphaDummy000) ∈
      (((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCphi (Class.cv (nb058AlphaDummy006))))))).fv ∪
        ((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCphi (Class.cv (nb058AlphaDummy006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0011 (x : Var) :
    x ∈
      (((Class.cab (nb058AlphaDummy007 x) (synWrex (nb058AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCphi (Class.cv (nb058AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb058AlphaDummy007 x) (synWrex (nb058AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCphi (Class.cv (nb058AlphaDummy008 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0012 :
    (nb058AlphaDummy006) ∈ (((Class.cv (nb058AlphaDummy006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0013 (x : Var) :
    (nb058AlphaDummy008 x) ∈ (((Class.cv (nb058AlphaDummy008 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0014 :
    (nb058AlphaDummy013) ∈
      (((Wff.classMem (Class.cv (nb058AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb058AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb058AlphaDummy013))).fv) :=
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

theorem nb058_support_mem_0015 (x : Var) :
    (nb058AlphaDummy015 x) ∈
      (((Wff.classMem (Class.cv (nb058AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb058AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb058AlphaDummy015 x))).fv) :=
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

theorem nb058_support_mem_0016 :
    (nb058AlphaDummy013) ∈
      (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0017 (x : Var) :
    (nb058AlphaDummy015 x) ∈
      (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0018 :
    (nb058AlphaDummy020) ∈
      (((synCnin (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy020))
            (Class.cv (nb058AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0019 (x : Var) :
    (nb058AlphaDummy023 x) ∈
      (((synCnin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0020 :
    (nb058AlphaDummy020) ∈
      (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0021 (x : Var) :
    (nb058AlphaDummy023 x) ∈
      (((Class.cv (nb058AlphaDummy023 x))).fv ∪ ((Class.cv (nb058AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0022 :
    (nb058AlphaDummy021) ∈
      (((synCnin (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy020))
            (Class.cv (nb058AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0023 (x : Var) :
    (nb058AlphaDummy024 x) ∈
      (((synCnin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0024 :
    (nb058AlphaDummy021) ∈
      (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0025 (x : Var) :
    (nb058AlphaDummy024 x) ∈
      (((Class.cv (nb058AlphaDummy023 x))).fv ∪ ((Class.cv (nb058AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0026 :
    (nb058AlphaDummy020) ∈
      (((synCcompl (Class.cv (nb058AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb058AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0027 (x : Var) :
    (nb058AlphaDummy023 x) ∈
      (((synCcompl (Class.cv (nb058AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb058AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
