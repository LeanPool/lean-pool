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

/-! Certificates from `NAR4C075C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_000`. -/
@[expose]
noncomputable def nb075AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_001`. -/
@[expose]
noncomputable def nb075AlphaDummy001 : Var :=
  (freshVar (({(nb075AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCrn (Class.cv (nb075AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_002`. -/
@[expose]
noncomputable def nb075AlphaDummy002 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCrn (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_003`. -/
@[expose]
noncomputable def nb075AlphaDummy003 : Var :=
  (freshVar
    (({(nb075AlphaDummy000)} : Finset Var) ∪ ({(nb075AlphaDummy001)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb075AlphaDummy000)) (synCvv))
          (Wff.classEq (Class.cv (nb075AlphaDummy001))
            (synCrn (Class.cv (nb075AlphaDummy000)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_004`. -/
@[expose]
noncomputable def nb075AlphaDummy004 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb075AlphaDummy002 x)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv x) (synCvv))
          (Wff.classEq (Class.cv (nb075AlphaDummy002 x)) (synCrn (Class.cv x))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_005`. -/
@[expose]
noncomputable def nb075AlphaDummy005 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_006`. -/
@[expose]
noncomputable def nb075AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_007`. -/
@[expose]
noncomputable def nb075AlphaDummy007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_008`. -/
@[expose]
noncomputable def nb075AlphaDummy008 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_009`. -/
@[expose]
noncomputable def nb075AlphaDummy009 : Var :=
  (freshVar (((synCcompl (Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCphi (Class.cv (nb075AlphaDummy006)))))))).fv ∪ ((synCcompl
          (Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_010`. -/
@[expose]
noncomputable def nb075AlphaDummy010 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCphi (Class.cv (nb075AlphaDummy008 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_011`. -/
@[expose]
noncomputable def nb075AlphaDummy011 : Var :=
  (freshVar (((Class.cab (nb075AlphaDummy005)
          (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
            (Wff.classEq (Class.cv (nb075AlphaDummy005))
              (synCphi (Class.cv (nb075AlphaDummy006))))))).fv ∪
      ((Class.cab (nb075AlphaDummy005)
          (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
            (Wff.classEq (Class.cv (nb075AlphaDummy005))
              (synCphi (Class.cv (nb075AlphaDummy006))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_012`. -/
@[expose]
noncomputable def nb075AlphaDummy012 (x : Var) : Var :=
  (freshVar (((Class.cab (nb075AlphaDummy007 x)
          (synWrex (nb075AlphaDummy008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
              (synCphi (Class.cv (nb075AlphaDummy008 x))))))).fv ∪
      ((Class.cab (nb075AlphaDummy007 x) (synWrex (nb075AlphaDummy008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
              (synCphi (Class.cv (nb075AlphaDummy008 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_013`. -/
@[expose]
noncomputable def nb075AlphaDummy013 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_014`. -/
@[expose]
noncomputable def nb075AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy006))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_015`. -/
@[expose]
noncomputable def nb075AlphaDummy015 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy008 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_016`. -/
@[expose]
noncomputable def nb075AlphaDummy016 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy008 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_017`. -/
@[expose]
noncomputable def nb075AlphaDummy017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb075AlphaDummy013)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb075AlphaDummy013)) (synC1c))).fv ∪
      ((Class.cv (nb075AlphaDummy013))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_018`. -/
@[expose]
noncomputable def nb075AlphaDummy018 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb075AlphaDummy015 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb075AlphaDummy015 x)) (synC1c))).fv ∪
      ((Class.cv (nb075AlphaDummy015 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_019`. -/
@[expose]
noncomputable def nb075AlphaDummy019 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_020`. -/
@[expose]
noncomputable def nb075AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_021`. -/
@[expose]
noncomputable def nb075AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_022`. -/
@[expose]
noncomputable def nb075AlphaDummy022 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_023`. -/
@[expose]
noncomputable def nb075AlphaDummy023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_024`. -/
@[expose]
noncomputable def nb075AlphaDummy024 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_025`. -/
@[expose]
noncomputable def nb075AlphaDummy025 : Var :=
  (freshVar (((synCnin (Class.cv (nb075AlphaDummy020))
          (Class.cv (nb075AlphaDummy021)))).fv ∪
      ((synCnin (Class.cv (nb075AlphaDummy020)) (Class.cv (nb075AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_026`. -/
@[expose]
noncomputable def nb075AlphaDummy026 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb075AlphaDummy023 x))
          (Class.cv (nb075AlphaDummy024 x)))).fv ∪
      ((synCnin (Class.cv (nb075AlphaDummy023 x)) (Class.cv (nb075AlphaDummy024 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_027`. -/
@[expose]
noncomputable def nb075AlphaDummy027 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_028`. -/
@[expose]
noncomputable def nb075AlphaDummy028 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy023 x))).fv ∪
      ((Class.cv (nb075AlphaDummy024 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_029`. -/
@[expose]
noncomputable def nb075AlphaDummy029 : Var :=
  (freshVar (((synCcompl (Class.cv (nb075AlphaDummy020)))).fv ∪
      ((synCcompl (Class.cv (nb075AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_030`. -/
@[expose]
noncomputable def nb075AlphaDummy030 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb075AlphaDummy023 x)))).fv ∪
      ((synCcompl (Class.cv (nb075AlphaDummy024 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_031`. -/
@[expose]
noncomputable def nb075AlphaDummy031 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_032`. -/
@[expose]
noncomputable def nb075AlphaDummy032 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy023 x))).fv ∪
      ((Class.cv (nb075AlphaDummy023 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_033`. -/
@[expose]
noncomputable def nb075AlphaDummy033 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy021))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_034`. -/
@[expose]
noncomputable def nb075AlphaDummy034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy024 x))).fv ∪
      ((Class.cv (nb075AlphaDummy024 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_035`. -/
@[expose]
noncomputable def nb075AlphaDummy035 : Var :=
  (freshVar (((Class.cab (nb075AlphaDummy005)
          (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
            (Wff.classEq (Class.cv (nb075AlphaDummy005))
              (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy005)
          (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
            (Wff.classEq (Class.cv (nb075AlphaDummy005))
              (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_036`. -/
@[expose]
noncomputable def nb075AlphaDummy036 (x : Var) : Var :=
  (freshVar (((Class.cab (nb075AlphaDummy007 x)
          (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
            (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
              (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy007 x)
          (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
            (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
              (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_037`. -/
@[expose]
noncomputable def nb075AlphaDummy037 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb075AlphaDummy006))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_038`. -/
@[expose]
noncomputable def nb075AlphaDummy038 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb075AlphaDummy008 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_039`. -/
@[expose]
noncomputable def nb075AlphaDummy039 : Var :=
  (freshVar (((synCphi (Class.cv (nb075AlphaDummy006)))).fv ∪
      ((synCphi (Class.cv (nb075AlphaDummy006)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_040`. -/
@[expose]
noncomputable def nb075AlphaDummy040 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb075AlphaDummy008 x)))).fv ∪
      ((synCphi (Class.cv (nb075AlphaDummy008 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_041`. -/
@[expose]
noncomputable def nb075AlphaDummy041 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_042`. -/
@[expose]
noncomputable def nb075AlphaDummy042 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_043`. -/
@[expose]
noncomputable def nb075AlphaDummy043 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_044`. -/
@[expose]
noncomputable def nb075AlphaDummy044 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_045`. -/
@[expose]
noncomputable def nb075AlphaDummy045 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_046`. -/
@[expose]
noncomputable def nb075AlphaDummy046 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_047`. -/
@[expose]
noncomputable def nb075AlphaDummy047 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy044 x))).fv ∪
      ((Class.cv (nb075AlphaDummy043 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_048`. -/
@[expose]
noncomputable def nb075AlphaDummy048 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy044 x))).fv ∪
      ((Class.cv (nb075AlphaDummy043 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_049`. -/
@[expose]
noncomputable def nb075AlphaDummy049 : Var :=
  (freshVar (((synCcompl (Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCphi (Class.cv (nb075AlphaDummy046)))))))).fv ∪ ((synCcompl
          (Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_050`. -/
@[expose]
noncomputable def nb075AlphaDummy050 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCphi (Class.cv (nb075AlphaDummy048 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_051`. -/
@[expose]
noncomputable def nb075AlphaDummy051 : Var :=
  (freshVar (((Class.cab (nb075AlphaDummy045)
          (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
            (Wff.classEq (Class.cv (nb075AlphaDummy045))
              (synCphi (Class.cv (nb075AlphaDummy046))))))).fv ∪
      ((Class.cab (nb075AlphaDummy045)
          (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
            (Wff.classEq (Class.cv (nb075AlphaDummy045))
              (synCphi (Class.cv (nb075AlphaDummy046))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_052`. -/
@[expose]
noncomputable def nb075AlphaDummy052 (x : Var) : Var :=
  (freshVar (((Class.cab (nb075AlphaDummy047 x)
          (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
            (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
              (synCphi (Class.cv (nb075AlphaDummy048 x))))))).fv ∪
      ((Class.cab (nb075AlphaDummy047 x)
          (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
            (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
              (synCphi (Class.cv (nb075AlphaDummy048 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_053`. -/
@[expose]
noncomputable def nb075AlphaDummy053 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy046))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_054`. -/
@[expose]
noncomputable def nb075AlphaDummy054 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy046))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_055`. -/
@[expose]
noncomputable def nb075AlphaDummy055 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy048 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_056`. -/
@[expose]
noncomputable def nb075AlphaDummy056 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy048 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_057`. -/
@[expose]
noncomputable def nb075AlphaDummy057 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb075AlphaDummy053)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb075AlphaDummy053)) (synC1c))).fv ∪
      ((Class.cv (nb075AlphaDummy053))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_058`. -/
@[expose]
noncomputable def nb075AlphaDummy058 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb075AlphaDummy055 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb075AlphaDummy055 x)) (synC1c))).fv ∪
      ((Class.cv (nb075AlphaDummy055 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_059`. -/
@[expose]
noncomputable def nb075AlphaDummy059 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_060`. -/
@[expose]
noncomputable def nb075AlphaDummy060 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_061`. -/
@[expose]
noncomputable def nb075AlphaDummy061 : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_062`. -/
@[expose]
noncomputable def nb075AlphaDummy062 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_063`. -/
@[expose]
noncomputable def nb075AlphaDummy063 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_064`. -/
@[expose]
noncomputable def nb075AlphaDummy064 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_065`. -/
@[expose]
noncomputable def nb075AlphaDummy065 : Var :=
  (freshVar (((synCnin (Class.cv (nb075AlphaDummy060))
          (Class.cv (nb075AlphaDummy061)))).fv ∪
      ((synCnin (Class.cv (nb075AlphaDummy060)) (Class.cv (nb075AlphaDummy061)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_066`. -/
@[expose]
noncomputable def nb075AlphaDummy066 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb075AlphaDummy063 x))
          (Class.cv (nb075AlphaDummy064 x)))).fv ∪
      ((synCnin (Class.cv (nb075AlphaDummy063 x)) (Class.cv (nb075AlphaDummy064 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_067`. -/
@[expose]
noncomputable def nb075AlphaDummy067 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_068`. -/
@[expose]
noncomputable def nb075AlphaDummy068 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy063 x))).fv ∪
      ((Class.cv (nb075AlphaDummy064 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_069`. -/
@[expose]
noncomputable def nb075AlphaDummy069 : Var :=
  (freshVar (((synCcompl (Class.cv (nb075AlphaDummy060)))).fv ∪
      ((synCcompl (Class.cv (nb075AlphaDummy061)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_070`. -/
@[expose]
noncomputable def nb075AlphaDummy070 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb075AlphaDummy063 x)))).fv ∪
      ((synCcompl (Class.cv (nb075AlphaDummy064 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_071`. -/
@[expose]
noncomputable def nb075AlphaDummy071 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy060))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_072`. -/
@[expose]
noncomputable def nb075AlphaDummy072 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy063 x))).fv ∪
      ((Class.cv (nb075AlphaDummy063 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_073`. -/
@[expose]
noncomputable def nb075AlphaDummy073 : Var :=
  (freshVar
    (((Class.cv (nb075AlphaDummy061))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_074`. -/
@[expose]
noncomputable def nb075AlphaDummy074 (x : Var) : Var :=
  (freshVar (((Class.cv (nb075AlphaDummy064 x))).fv ∪
      ((Class.cv (nb075AlphaDummy064 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_075`. -/
@[expose]
noncomputable def nb075AlphaDummy075 : Var :=
  (freshVar (((Class.cab (nb075AlphaDummy045)
          (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
            (Wff.classEq (Class.cv (nb075AlphaDummy045))
              (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy045)
          (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
            (Wff.classEq (Class.cv (nb075AlphaDummy045))
              (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_076`. -/
@[expose]
noncomputable def nb075AlphaDummy076 (x : Var) : Var :=
  (freshVar (((Class.cab (nb075AlphaDummy047 x)
          (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
            (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
              (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy047 x)
          (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
            (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
              (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_077`. -/
@[expose]
noncomputable def nb075AlphaDummy077 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb075AlphaDummy046))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_078`. -/
@[expose]
noncomputable def nb075AlphaDummy078 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb075AlphaDummy048 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_079`. -/
@[expose]
noncomputable def nb075AlphaDummy079 : Var :=
  (freshVar (((synCphi (Class.cv (nb075AlphaDummy046)))).fv ∪
      ((synCphi (Class.cv (nb075AlphaDummy046)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb075_alpha_dummy_080`. -/
@[expose]
noncomputable def nb075AlphaDummy080 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb075AlphaDummy048 x)))).fv ∪
      ((synCphi (Class.cv (nb075AlphaDummy048 x)))).fv) 0)

theorem nb075_fresh_000 :
    (nb075AlphaDummy011) ∉
      (((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCphi (Class.cv (nb075AlphaDummy006))))))).fv ∪
        ((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCphi (Class.cv (nb075AlphaDummy006))))))).fv) :=
  by
  simpa only [nb075AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCphi (Class.cv (nb075AlphaDummy006))))))).fv ∪
        ((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCphi (Class.cv (nb075AlphaDummy006))))))).fv)
      0

theorem nb075_fresh_001 :
    (nb075AlphaDummy035) ∉
      (((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb075AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb075_fresh_002 (x : Var) :
    (nb075AlphaDummy036 x) ∉
      (((Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb075AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb075_fresh_003 (x : Var) :
    (nb075AlphaDummy012 x) ∉
      (((Class.cab (nb075AlphaDummy007 x) (synWrex (nb075AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCphi (Class.cv (nb075AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb075AlphaDummy007 x) (synWrex (nb075AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCphi (Class.cv (nb075AlphaDummy008 x))))))).fv) :=
  by
  simpa only [nb075AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb075AlphaDummy007 x) (synWrex (nb075AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCphi (Class.cv (nb075AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb075AlphaDummy007 x) (synWrex (nb075AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCphi (Class.cv (nb075AlphaDummy008 x))))))).fv)
      0

theorem nb075_fresh_004 :
    (nb075AlphaDummy075) ∉
      (((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb075AlphaDummy075] using
    freshVar_not_mem
      (((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb075_fresh_005 :
    (nb075AlphaDummy051) ∉
      (((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCphi (Class.cv (nb075AlphaDummy046))))))).fv ∪
        ((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCphi (Class.cv (nb075AlphaDummy046))))))).fv) :=
  by
  simpa only [nb075AlphaDummy051] using
    freshVar_not_mem
      (((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCphi (Class.cv (nb075AlphaDummy046))))))).fv ∪
        ((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCphi (Class.cv (nb075AlphaDummy046))))))).fv)
      0

theorem nb075_fresh_006 (x : Var) :
    (nb075AlphaDummy076 x) ∉
      (((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb075AlphaDummy076] using
    freshVar_not_mem
      (((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb075_fresh_007 (x : Var) :
    (nb075AlphaDummy052 x) ∉
      (((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCphi (Class.cv (nb075AlphaDummy048 x))))))).fv ∪
        ((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCphi (Class.cv (nb075AlphaDummy048 x))))))).fv) :=
  by
  simpa only [nb075AlphaDummy052] using
    freshVar_not_mem
      (((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCphi (Class.cv (nb075AlphaDummy048 x))))))).fv ∪
        ((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCphi (Class.cv (nb075AlphaDummy048 x))))))).fv)
      0

theorem nb075_fresh_008 :
    (nb075AlphaDummy005) ∉
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv) :=
  by
  simpa only [nb075AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv)
      0

theorem nb075_fresh_009 :
    (nb075AlphaDummy006) ∉
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv) :=
  by
  simpa only [nb075AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv)
      1

theorem nb075_distinct_010 : (nb075AlphaDummy005) ≠ (nb075AlphaDummy006) := by
  simpa only [nb075AlphaDummy005, nb075AlphaDummy006] using
    (freshVar_injective
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb075_fresh_011 :
    (nb075AlphaDummy041) ∉
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb075AlphaDummy041] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) 0

theorem nb075_fresh_012 :
    (nb075AlphaDummy042) ∉
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb075AlphaDummy042] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) 1

theorem nb075_distinct_013 : (nb075AlphaDummy041) ≠ (nb075AlphaDummy042) := by
  simpa only [nb075AlphaDummy041, nb075AlphaDummy042] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_fresh_014 :
    (nb075AlphaDummy013) ∉ (((Class.cv (nb075AlphaDummy006))).fv) := by
  simpa only [nb075AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy006))).fv) 0

theorem nb075_fresh_015 :
    (nb075AlphaDummy014) ∉ (((Class.cv (nb075AlphaDummy006))).fv) := by
  simpa only [nb075AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy006))).fv) 1

theorem nb075_distinct_016 : (nb075AlphaDummy013) ≠ (nb075AlphaDummy014) := by
  simpa only [nb075AlphaDummy013, nb075AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy006))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_017 (x : Var) :
    (nb075AlphaDummy015 x) ∉ (((Class.cv (nb075AlphaDummy008 x))).fv) := by
  simpa only [nb075AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy008 x))).fv) 0

theorem nb075_fresh_018 (x : Var) :
    (nb075AlphaDummy016 x) ∉ (((Class.cv (nb075AlphaDummy008 x))).fv) := by
  simpa only [nb075AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy008 x))).fv) 1

theorem nb075_distinct_019 (x : Var) :
    (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy016 x) := by
  simpa only [nb075AlphaDummy015, nb075AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy008 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb075_fresh_020 :
    (nb075AlphaDummy019) ∉
      (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) 0

theorem nb075_fresh_021 :
    (nb075AlphaDummy020) ∉
      (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) 1

theorem nb075_fresh_022 :
    (nb075AlphaDummy021) ∉
      (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) 2

theorem nb075_distinct_023 : (nb075AlphaDummy019) ≠ (nb075AlphaDummy020) := by
  simpa only [nb075AlphaDummy019, nb075AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_distinct_024 : (nb075AlphaDummy019) ≠ (nb075AlphaDummy021) := by
  simpa only [nb075AlphaDummy019, nb075AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb075_distinct_025 : (nb075AlphaDummy020) ≠ (nb075AlphaDummy021) := by
  simpa only [nb075AlphaDummy020, nb075AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb075_fresh_026 (x : Var) :
    (nb075AlphaDummy022 x) ∉
      (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 0

theorem nb075_fresh_027 (x : Var) :
    (nb075AlphaDummy023 x) ∉
      (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 1

theorem nb075_fresh_028 (x : Var) :
    (nb075AlphaDummy024 x) ∉
      (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 2

theorem nb075_distinct_029 (x : Var) :
    (nb075AlphaDummy022 x) ≠ (nb075AlphaDummy023 x) := by
  simpa only [nb075AlphaDummy022, nb075AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_distinct_030 (x : Var) :
    (nb075AlphaDummy022 x) ≠ (nb075AlphaDummy024 x) := by
  simpa only [nb075AlphaDummy022, nb075AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb075_distinct_031 (x : Var) :
    (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy024 x) := by
  simpa only [nb075AlphaDummy023, nb075AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb075_fresh_032 :
    (nb075AlphaDummy031) ∉
      (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy020))).fv) :=
  by
  simpa only [nb075AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy020))).fv)
      0

theorem nb075_fresh_033 :
    (nb075AlphaDummy027) ∉
      (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv) :=
  by
  simpa only [nb075AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv)
      0

theorem nb075_fresh_034 :
    (nb075AlphaDummy033) ∉
      (((Class.cv (nb075AlphaDummy021))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv) :=
  by
  simpa only [nb075AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy021))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv)
      0

theorem nb075_fresh_035 (x : Var) :
    (nb075AlphaDummy032 x) ∉
      (((Class.cv (nb075AlphaDummy023 x))).fv ∪ ((Class.cv (nb075AlphaDummy023 x))).fv) :=
  by
  simpa only [nb075AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy023 x))).fv ∪ ((Class.cv (nb075AlphaDummy023 x))).fv)
      0

theorem nb075_fresh_036 (x : Var) :
    (nb075AlphaDummy028 x) ∉
      (((Class.cv (nb075AlphaDummy023 x))).fv ∪ ((Class.cv (nb075AlphaDummy024 x))).fv) :=
  by
  simpa only [nb075AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy023 x))).fv ∪ ((Class.cv (nb075AlphaDummy024 x))).fv)
      0

theorem nb075_fresh_037 (x : Var) :
    (nb075AlphaDummy034 x) ∉
      (((Class.cv (nb075AlphaDummy024 x))).fv ∪ ((Class.cv (nb075AlphaDummy024 x))).fv) :=
  by
  simpa only [nb075AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy024 x))).fv ∪ ((Class.cv (nb075AlphaDummy024 x))).fv)
      0

theorem nb075_fresh_038 :
    (nb075AlphaDummy045) ∉
      (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv) :=
  by
  simpa only [nb075AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv)
      0

theorem nb075_fresh_039 :
    (nb075AlphaDummy046) ∉
      (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv) :=
  by
  simpa only [nb075AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv)
      1

theorem nb075_distinct_040 : (nb075AlphaDummy045) ≠ (nb075AlphaDummy046) := by
  simpa only [nb075AlphaDummy045, nb075AlphaDummy046] using
    (freshVar_injective
      (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb075_fresh_041 (x : Var) :
    (nb075AlphaDummy047 x) ∉
      (((Class.cv (nb075AlphaDummy044 x))).fv ∪ ((Class.cv (nb075AlphaDummy043 x))).fv) :=
  by
  simpa only [nb075AlphaDummy047] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy044 x))).fv ∪ ((Class.cv (nb075AlphaDummy043 x))).fv)
      0

theorem nb075_fresh_042 (x : Var) :
    (nb075AlphaDummy048 x) ∉
      (((Class.cv (nb075AlphaDummy044 x))).fv ∪ ((Class.cv (nb075AlphaDummy043 x))).fv) :=
  by
  simpa only [nb075AlphaDummy048] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy044 x))).fv ∪ ((Class.cv (nb075AlphaDummy043 x))).fv)
      1

theorem nb075_distinct_043 (x : Var) :
    (nb075AlphaDummy047 x) ≠ (nb075AlphaDummy048 x) := by
  simpa only [nb075AlphaDummy047, nb075AlphaDummy048] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy044 x))).fv ∪
        ((Class.cv (nb075AlphaDummy043 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_044 :
    (nb075AlphaDummy053) ∉ (((Class.cv (nb075AlphaDummy046))).fv) := by
  simpa only [nb075AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy046))).fv) 0

theorem nb075_fresh_045 :
    (nb075AlphaDummy054) ∉ (((Class.cv (nb075AlphaDummy046))).fv) := by
  simpa only [nb075AlphaDummy054] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy046))).fv) 1

theorem nb075_distinct_046 : (nb075AlphaDummy053) ≠ (nb075AlphaDummy054) := by
  simpa only [nb075AlphaDummy053, nb075AlphaDummy054] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy046))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_047 (x : Var) :
    (nb075AlphaDummy055 x) ∉ (((Class.cv (nb075AlphaDummy048 x))).fv) := by
  simpa only [nb075AlphaDummy055] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy048 x))).fv) 0

theorem nb075_fresh_048 (x : Var) :
    (nb075AlphaDummy056 x) ∉ (((Class.cv (nb075AlphaDummy048 x))).fv) := by
  simpa only [nb075AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy048 x))).fv) 1

theorem nb075_distinct_049 (x : Var) :
    (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy056 x) := by
  simpa only [nb075AlphaDummy055, nb075AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy048 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb075_fresh_050 :
    (nb075AlphaDummy059) ∉
      (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) 0

theorem nb075_fresh_051 :
    (nb075AlphaDummy060) ∉
      (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) 1

theorem nb075_fresh_052 :
    (nb075AlphaDummy061) ∉
      (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) 2

theorem nb075_distinct_053 : (nb075AlphaDummy059) ≠ (nb075AlphaDummy060) := by
  simpa only [nb075AlphaDummy059, nb075AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_distinct_054 : (nb075AlphaDummy059) ≠ (nb075AlphaDummy061) := by
  simpa only [nb075AlphaDummy059, nb075AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb075_distinct_055 : (nb075AlphaDummy060) ≠ (nb075AlphaDummy061) := by
  simpa only [nb075AlphaDummy060, nb075AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb075_fresh_056 (x : Var) :
    (nb075AlphaDummy062 x) ∉
      (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 0

theorem nb075_fresh_057 (x : Var) :
    (nb075AlphaDummy063 x) ∉
      (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 1

theorem nb075_fresh_058 (x : Var) :
    (nb075AlphaDummy064 x) ∉
      (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb075AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 2

theorem nb075_distinct_059 (x : Var) :
    (nb075AlphaDummy062 x) ≠ (nb075AlphaDummy063 x) := by
  simpa only [nb075AlphaDummy062, nb075AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb075_distinct_060 (x : Var) :
    (nb075AlphaDummy062 x) ≠ (nb075AlphaDummy064 x) := by
  simpa only [nb075AlphaDummy062, nb075AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb075_distinct_061 (x : Var) :
    (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy064 x) := by
  simpa only [nb075AlphaDummy063, nb075AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb075_fresh_062 :
    (nb075AlphaDummy071) ∉
      (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy060))).fv) :=
  by
  simpa only [nb075AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy060))).fv)
      0

theorem nb075_fresh_063 :
    (nb075AlphaDummy067) ∉
      (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv) :=
  by
  simpa only [nb075AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv)
      0

theorem nb075_fresh_064 :
    (nb075AlphaDummy073) ∉
      (((Class.cv (nb075AlphaDummy061))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv) :=
  by
  simpa only [nb075AlphaDummy073] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy061))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv)
      0

theorem nb075_fresh_065 (x : Var) :
    (nb075AlphaDummy072 x) ∉
      (((Class.cv (nb075AlphaDummy063 x))).fv ∪ ((Class.cv (nb075AlphaDummy063 x))).fv) :=
  by
  simpa only [nb075AlphaDummy072] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy063 x))).fv ∪ ((Class.cv (nb075AlphaDummy063 x))).fv)
      0

theorem nb075_fresh_066 (x : Var) :
    (nb075AlphaDummy068 x) ∉
      (((Class.cv (nb075AlphaDummy063 x))).fv ∪ ((Class.cv (nb075AlphaDummy064 x))).fv) :=
  by
  simpa only [nb075AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy063 x))).fv ∪ ((Class.cv (nb075AlphaDummy064 x))).fv)
      0

theorem nb075_fresh_067 (x : Var) :
    (nb075AlphaDummy074 x) ∉
      (((Class.cv (nb075AlphaDummy064 x))).fv ∪ ((Class.cv (nb075AlphaDummy064 x))).fv) :=
  by
  simpa only [nb075AlphaDummy074] using
    freshVar_not_mem
      (((Class.cv (nb075AlphaDummy064 x))).fv ∪ ((Class.cv (nb075AlphaDummy064 x))).fv)
      0

theorem nb075_fresh_068 (x : Var) :
    (nb075AlphaDummy007 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) :=
  by
  simpa only [nb075AlphaDummy007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C075C001Part002`. -/


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

theorem nb075_fresh_069 (x : Var) :
    (nb075AlphaDummy008 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) :=
  by
  simpa only [nb075AlphaDummy008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) 1

theorem nb075_distinct_070 (x : Var) :
    (nb075AlphaDummy007 x) ≠ (nb075AlphaDummy008 x) := by
  simpa only [nb075AlphaDummy007, nb075AlphaDummy008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb075_fresh_071 (x : Var) :
    (nb075AlphaDummy043 x) ∉ (((Class.cv x)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb075AlphaDummy043] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((synCvv)).fv) 0

theorem nb075_fresh_072 (x : Var) :
    (nb075AlphaDummy044 x) ∉ (((Class.cv x)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb075AlphaDummy044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((synCvv)).fv) 1

theorem nb075_distinct_073 (x : Var) :
    (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy044 x) := by
  simpa only [nb075AlphaDummy043, nb075AlphaDummy044] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((synCvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_074 :
    (nb075AlphaDummy017) ∉
      (((Wff.classMem (Class.cv (nb075AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy013))).fv) :=
  by
  simpa only [nb075AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb075AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy013))).fv)
      0

theorem nb075_fresh_075 (x : Var) :
    (nb075AlphaDummy018 x) ∉
      (((Wff.classMem (Class.cv (nb075AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy015 x))).fv) :=
  by
  simpa only [nb075AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb075AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy015 x))).fv)
      0

theorem nb075_fresh_076 :
    (nb075AlphaDummy057) ∉
      (((Wff.classMem (Class.cv (nb075AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy053))).fv) :=
  by
  simpa only [nb075AlphaDummy057] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb075AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy053))).fv)
      0

theorem nb075_fresh_077 (x : Var) :
    (nb075AlphaDummy058 x) ∉
      (((Wff.classMem (Class.cv (nb075AlphaDummy055 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy055 x)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy055 x))).fv) :=
  by
  simpa only [nb075AlphaDummy058] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb075AlphaDummy055 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy055 x)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy055 x))).fv)
      0

theorem nb075_fresh_078 :
    (nb075AlphaDummy009) ∉
      (((synCcompl (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCphi (Class.cv (nb075AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb075AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCphi (Class.cv (nb075AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb075_fresh_079 (x : Var) :
    (nb075AlphaDummy010 x) ∉
      (((synCcompl (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCphi (Class.cv (nb075AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb075AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCphi (Class.cv (nb075AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb075_fresh_080 :
    (nb075AlphaDummy049) ∉
      (((synCcompl (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCphi (Class.cv (nb075AlphaDummy046)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb075AlphaDummy049] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCphi (Class.cv (nb075AlphaDummy046)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb075_fresh_081 (x : Var) :
    (nb075AlphaDummy050 x) ∉
      (((synCcompl (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCphi (Class.cv (nb075AlphaDummy048 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb075AlphaDummy050] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCphi (Class.cv (nb075AlphaDummy048 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb075_fresh_082 :
    (nb075AlphaDummy029) ∉
      (((synCcompl (Class.cv (nb075AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy021)))).fv) :=
  by
  simpa only [nb075AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb075AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy021)))).fv)
      0

theorem nb075_fresh_083 (x : Var) :
    (nb075AlphaDummy030 x) ∉
      (((synCcompl (Class.cv (nb075AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy024 x)))).fv) :=
  by
  simpa only [nb075AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb075AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy024 x)))).fv)
      0

theorem nb075_fresh_084 :
    (nb075AlphaDummy069) ∉
      (((synCcompl (Class.cv (nb075AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy061)))).fv) :=
  by
  simpa only [nb075AlphaDummy069] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb075AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy061)))).fv)
      0

theorem nb075_fresh_085 (x : Var) :
    (nb075AlphaDummy070 x) ∉
      (((synCcompl (Class.cv (nb075AlphaDummy063 x)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy064 x)))).fv) :=
  by
  simpa only [nb075AlphaDummy070] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb075AlphaDummy063 x)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy064 x)))).fv)
      0

theorem nb075_fresh_086 :
    (nb075AlphaDummy037) ∉
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb075AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb075_fresh_087 (x : Var) :
    (nb075AlphaDummy038 x) ∉
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb075AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb075_fresh_088 :
    (nb075AlphaDummy077) ∉
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy046))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb075AlphaDummy077] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy046))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb075_fresh_089 (x : Var) :
    (nb075AlphaDummy078 x) ∉
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy048 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb075AlphaDummy078] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy048 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb075_fresh_090 :
    (nb075AlphaDummy025) ∉
      (((synCnin (Class.cv (nb075AlphaDummy020)) (Class.cv (nb075AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy020))
            (Class.cv (nb075AlphaDummy021)))).fv) :=
  by
  simpa only [nb075AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb075AlphaDummy020)) (Class.cv (nb075AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy020)) (Class.cv (nb075AlphaDummy021)))).fv)
      0

theorem nb075_fresh_091 (x : Var) :
    (nb075AlphaDummy026 x) ∉
      (((synCnin (Class.cv (nb075AlphaDummy023 x))
            (Class.cv (nb075AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy023 x))
            (Class.cv (nb075AlphaDummy024 x)))).fv) :=
  by
  simpa only [nb075AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb075AlphaDummy023 x))
            (Class.cv (nb075AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy023 x))
            (Class.cv (nb075AlphaDummy024 x)))).fv)
      0

theorem nb075_fresh_092 :
    (nb075AlphaDummy065) ∉
      (((synCnin (Class.cv (nb075AlphaDummy060)) (Class.cv (nb075AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy060))
            (Class.cv (nb075AlphaDummy061)))).fv) :=
  by
  simpa only [nb075AlphaDummy065] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb075AlphaDummy060)) (Class.cv (nb075AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy060)) (Class.cv (nb075AlphaDummy061)))).fv)
      0

theorem nb075_fresh_093 (x : Var) :
    (nb075AlphaDummy066 x) ∉
      (((synCnin (Class.cv (nb075AlphaDummy063 x))
            (Class.cv (nb075AlphaDummy064 x)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy063 x))
            (Class.cv (nb075AlphaDummy064 x)))).fv) :=
  by
  simpa only [nb075AlphaDummy066] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb075AlphaDummy063 x))
            (Class.cv (nb075AlphaDummy064 x)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy063 x))
            (Class.cv (nb075AlphaDummy064 x)))).fv)
      0

theorem nb075_fresh_094 :
    (nb075AlphaDummy039) ∉
      (((synCphi (Class.cv (nb075AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy006)))).fv) :=
  by
  simpa only [nb075AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb075AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy006)))).fv)
      0

theorem nb075_fresh_095 (x : Var) :
    (nb075AlphaDummy040 x) ∉
      (((synCphi (Class.cv (nb075AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy008 x)))).fv) :=
  by
  simpa only [nb075AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb075AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy008 x)))).fv)
      0

theorem nb075_fresh_096 :
    (nb075AlphaDummy079) ∉
      (((synCphi (Class.cv (nb075AlphaDummy046)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy046)))).fv) :=
  by
  simpa only [nb075AlphaDummy079] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb075AlphaDummy046)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy046)))).fv)
      0

theorem nb075_fresh_097 (x : Var) :
    (nb075AlphaDummy080 x) ∉
      (((synCphi (Class.cv (nb075AlphaDummy048 x)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy048 x)))).fv) :=
  by
  simpa only [nb075AlphaDummy080] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb075AlphaDummy048 x)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy048 x)))).fv)
      0

theorem nb075_fresh_098 :
    (nb075AlphaDummy001) ∉
      (({(nb075AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCrn (Class.cv (nb075AlphaDummy000)))).fv) :=
  by
  simpa only [nb075AlphaDummy001] using
    freshVar_not_mem
      (({(nb075AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCrn (Class.cv (nb075AlphaDummy000)))).fv)
      0

theorem nb075_fresh_099 :
    (nb075AlphaDummy003) ∉
      (({(nb075AlphaDummy000)} : Finset Var) ∪ ({(nb075AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb075AlphaDummy000)) (synCvv))
            (Wff.classEq (Class.cv (nb075AlphaDummy001))
              (synCrn (Class.cv (nb075AlphaDummy000)))))).fv) :=
  by
  simpa only [nb075AlphaDummy003] using
    freshVar_not_mem
      (({(nb075AlphaDummy000)} : Finset Var) ∪ ({(nb075AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb075AlphaDummy000)) (synCvv))
            (Wff.classEq (Class.cv (nb075AlphaDummy001))
              (synCrn (Class.cv (nb075AlphaDummy000)))))).fv)
      0

theorem nb075_fresh_100 (x : Var) :
    (nb075AlphaDummy002 x) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCrn (Class.cv x))).fv) :=
  by
  simpa only [nb075AlphaDummy002] using
    freshVar_not_mem (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCrn (Class.cv x))).fv)
      0

theorem nb075_fresh_101 (x : Var) :
    (nb075AlphaDummy004 x) ∉
      (({ x } : Finset Var) ∪ ({(nb075AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb075AlphaDummy002 x)) (synCrn (Class.cv x))))).fv) :=
  by
  simpa only [nb075AlphaDummy004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb075AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb075AlphaDummy002 x)) (synCrn (Class.cv x))))).fv)
      0

theorem nb075_fresh_102 : (nb075AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb075AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb075_support_mem_0000 :
    (nb075AlphaDummy000) ∈
      (({(nb075AlphaDummy000)} : Finset Var) ∪ ({(nb075AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb075AlphaDummy000)) (synCvv))
            (Wff.classEq (Class.cv (nb075AlphaDummy001))
              (synCrn (Class.cv (nb075AlphaDummy000)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0001 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb075AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb075AlphaDummy002 x)) (synCrn (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0002 :
    (nb075AlphaDummy001) ∈
      (({(nb075AlphaDummy000)} : Finset Var) ∪ ({(nb075AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb075AlphaDummy000)) (synCvv))
            (Wff.classEq (Class.cv (nb075AlphaDummy001))
              (synCrn (Class.cv (nb075AlphaDummy000)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0003 (x : Var) :
    (nb075AlphaDummy002 x) ∈
      (({ x } : Finset Var) ∪ ({(nb075AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb075AlphaDummy002 x)) (synCrn (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0004 :
    (nb075AlphaDummy000) ∈
      (({(nb075AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCrn (Class.cv (nb075AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0005 (x : Var) :
    x ∈ (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCrn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0006 :
    (nb075AlphaDummy000) ∈
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0007 :
    (nb075AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCphi (Class.cv (nb075AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy005) from (by
          unfold nb075AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy006) from (by
            unfold nb075AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0008 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0009 (x : Var) :
    x ∈
      (((synCcompl (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCphi (Class.cv (nb075AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb075AlphaDummy007 x) from (by
          unfold nb075AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb075AlphaDummy008 x) from (by
            unfold nb075AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0010 :
    (nb075AlphaDummy000) ∈
      (((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCphi (Class.cv (nb075AlphaDummy006))))))).fv ∪
        ((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCphi (Class.cv (nb075AlphaDummy006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy005) from (by
          unfold nb075AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy006) from (by
            unfold nb075AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0011 (x : Var) :
    x ∈
      (((Class.cab (nb075AlphaDummy007 x) (synWrex (nb075AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCphi (Class.cv (nb075AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb075AlphaDummy007 x) (synWrex (nb075AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCphi (Class.cv (nb075AlphaDummy008 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb075AlphaDummy007 x) from (by
          unfold nb075AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb075AlphaDummy008 x) from (by
            unfold nb075AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0012 :
    (nb075AlphaDummy006) ∈ (((Class.cv (nb075AlphaDummy006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0013 (x : Var) :
    (nb075AlphaDummy008 x) ∈ (((Class.cv (nb075AlphaDummy008 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0014 :
    (nb075AlphaDummy013) ∈
      (((Wff.classMem (Class.cv (nb075AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy013))).fv) :=
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

theorem nb075_support_mem_0015 (x : Var) :
    (nb075AlphaDummy015 x) ∈
      (((Wff.classMem (Class.cv (nb075AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy015 x))).fv) :=
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

theorem nb075_support_mem_0016 :
    (nb075AlphaDummy013) ∈
      (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0017 (x : Var) :
    (nb075AlphaDummy015 x) ∈
      (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0018 :
    (nb075AlphaDummy020) ∈
      (((synCnin (Class.cv (nb075AlphaDummy020)) (Class.cv (nb075AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy020))
            (Class.cv (nb075AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0019 (x : Var) :
    (nb075AlphaDummy023 x) ∈
      (((synCnin (Class.cv (nb075AlphaDummy023 x))
            (Class.cv (nb075AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy023 x))
            (Class.cv (nb075AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0020 :
    (nb075AlphaDummy020) ∈
      (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0021 (x : Var) :
    (nb075AlphaDummy023 x) ∈
      (((Class.cv (nb075AlphaDummy023 x))).fv ∪ ((Class.cv (nb075AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0022 :
    (nb075AlphaDummy021) ∈
      (((synCnin (Class.cv (nb075AlphaDummy020)) (Class.cv (nb075AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy020))
            (Class.cv (nb075AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0023 (x : Var) :
    (nb075AlphaDummy024 x) ∈
      (((synCnin (Class.cv (nb075AlphaDummy023 x))
            (Class.cv (nb075AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy023 x))
            (Class.cv (nb075AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0024 :
    (nb075AlphaDummy021) ∈
      (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0025 (x : Var) :
    (nb075AlphaDummy024 x) ∈
      (((Class.cv (nb075AlphaDummy023 x))).fv ∪ ((Class.cv (nb075AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0026 :
    (nb075AlphaDummy020) ∈
      (((synCcompl (Class.cv (nb075AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0027 (x : Var) :
    (nb075AlphaDummy023 x) ∈
      (((synCcompl (Class.cv (nb075AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0028 :
    (nb075AlphaDummy020) ∈
      (((Class.cv (nb075AlphaDummy020))).fv ∪ ((Class.cv (nb075AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0029 (x : Var) :
    (nb075AlphaDummy023 x) ∈
      (((Class.cv (nb075AlphaDummy023 x))).fv ∪ ((Class.cv (nb075AlphaDummy023 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0030 :
    (nb075AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb075AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0031 (x : Var) :
    (nb075AlphaDummy024 x) ∈
      (((synCcompl (Class.cv (nb075AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0032 :
    (nb075AlphaDummy021) ∈
      (((Class.cv (nb075AlphaDummy021))).fv ∪ ((Class.cv (nb075AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0033 (x : Var) :
    (nb075AlphaDummy024 x) ∈
      (((Class.cv (nb075AlphaDummy024 x))).fv ∪ ((Class.cv (nb075AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0034 :
    (nb075AlphaDummy001) ∈
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((Class.cv (nb075AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0035 :
    (nb075AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy000))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCphi (Class.cv (nb075AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy005) from (by
          unfold nb075AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy006) from (by
            unfold nb075AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0036 (x : Var) :
    (nb075AlphaDummy002 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0037 (x : Var) :
    (nb075AlphaDummy002 x) ∈
      (((synCcompl (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCphi (Class.cv (nb075AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy007 x) from (by
          unfold nb075AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy008 x) from (by
            unfold nb075AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0038 :
    (nb075AlphaDummy001) ∈
      (((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy005) from (by
          unfold nb075AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy006) from (by
            unfold nb075AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0039 (x : Var) :
    (nb075AlphaDummy002 x) ∈
      (((Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy007 x) from (by
          unfold nb075AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy008 x) from (by
            unfold nb075AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0040 :
    (nb075AlphaDummy006) ∈
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0041 (x : Var) :
    (nb075AlphaDummy008 x) ∈
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0042 :
    (nb075AlphaDummy006) ∈
      (((synCphi (Class.cv (nb075AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0043 (x : Var) :
    (nb075AlphaDummy008 x) ∈
      (((synCphi (Class.cv (nb075AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy008 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0044 :
    (nb075AlphaDummy042) ∈
      (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0045 :
    (nb075AlphaDummy042) ∈
      (((synCcompl (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCphi (Class.cv (nb075AlphaDummy046)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy045) from (by
          unfold nb075AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy046) from (by
            unfold nb075AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0044) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0046 (x : Var) :
    (nb075AlphaDummy044 x) ∈
      (((Class.cv (nb075AlphaDummy044 x))).fv ∪ ((Class.cv (nb075AlphaDummy043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0047 (x : Var) :
    (nb075AlphaDummy044 x) ∈
      (((synCcompl (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCphi (Class.cv (nb075AlphaDummy048 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy047 x) from (by
          unfold nb075AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0046 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy048 x) from (by
            unfold nb075AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0046 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0048 :
    (nb075AlphaDummy042) ∈
      (((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCphi (Class.cv (nb075AlphaDummy046))))))).fv ∪
        ((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCphi (Class.cv (nb075AlphaDummy046))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy045) from (by
          unfold nb075AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy046) from (by
            unfold nb075AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0044) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0049 (x : Var) :
    (nb075AlphaDummy044 x) ∈
      (((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCphi (Class.cv (nb075AlphaDummy048 x))))))).fv ∪
        ((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCphi (Class.cv (nb075AlphaDummy048 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy047 x) from (by
          unfold nb075AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0046 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy048 x) from (by
            unfold nb075AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0046 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0050 :
    (nb075AlphaDummy046) ∈ (((Class.cv (nb075AlphaDummy046))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0051 (x : Var) :
    (nb075AlphaDummy048 x) ∈ (((Class.cv (nb075AlphaDummy048 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0052 :
    (nb075AlphaDummy053) ∈
      (((Wff.classMem (Class.cv (nb075AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy053))).fv) :=
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

theorem nb075_support_mem_0053 (x : Var) :
    (nb075AlphaDummy055 x) ∈
      (((Wff.classMem (Class.cv (nb075AlphaDummy055 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb075AlphaDummy055 x)) (synC1c))).fv ∪
        ((Class.cv (nb075AlphaDummy055 x))).fv) :=
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

theorem nb075_support_mem_0054 :
    (nb075AlphaDummy053) ∈
      (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0055 (x : Var) :
    (nb075AlphaDummy055 x) ∈
      (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0056 :
    (nb075AlphaDummy060) ∈
      (((synCnin (Class.cv (nb075AlphaDummy060)) (Class.cv (nb075AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy060))
            (Class.cv (nb075AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0057 (x : Var) :
    (nb075AlphaDummy063 x) ∈
      (((synCnin (Class.cv (nb075AlphaDummy063 x))
            (Class.cv (nb075AlphaDummy064 x)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy063 x))
            (Class.cv (nb075AlphaDummy064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0058 :
    (nb075AlphaDummy060) ∈
      (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0059 (x : Var) :
    (nb075AlphaDummy063 x) ∈
      (((Class.cv (nb075AlphaDummy063 x))).fv ∪ ((Class.cv (nb075AlphaDummy064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0060 :
    (nb075AlphaDummy061) ∈
      (((synCnin (Class.cv (nb075AlphaDummy060)) (Class.cv (nb075AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy060))
            (Class.cv (nb075AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0061 (x : Var) :
    (nb075AlphaDummy064 x) ∈
      (((synCnin (Class.cv (nb075AlphaDummy063 x))
            (Class.cv (nb075AlphaDummy064 x)))).fv ∪
        ((synCnin (Class.cv (nb075AlphaDummy063 x))
            (Class.cv (nb075AlphaDummy064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0062 :
    (nb075AlphaDummy061) ∈
      (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0063 (x : Var) :
    (nb075AlphaDummy064 x) ∈
      (((Class.cv (nb075AlphaDummy063 x))).fv ∪ ((Class.cv (nb075AlphaDummy064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0064 :
    (nb075AlphaDummy060) ∈
      (((synCcompl (Class.cv (nb075AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0065 (x : Var) :
    (nb075AlphaDummy063 x) ∈
      (((synCcompl (Class.cv (nb075AlphaDummy063 x)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0066 :
    (nb075AlphaDummy060) ∈
      (((Class.cv (nb075AlphaDummy060))).fv ∪ ((Class.cv (nb075AlphaDummy060))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0067 (x : Var) :
    (nb075AlphaDummy063 x) ∈
      (((Class.cv (nb075AlphaDummy063 x))).fv ∪ ((Class.cv (nb075AlphaDummy063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0068 :
    (nb075AlphaDummy061) ∈
      (((synCcompl (Class.cv (nb075AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0069 (x : Var) :
    (nb075AlphaDummy064 x) ∈
      (((synCcompl (Class.cv (nb075AlphaDummy063 x)))).fv ∪
        ((synCcompl (Class.cv (nb075AlphaDummy064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0070 :
    (nb075AlphaDummy061) ∈
      (((Class.cv (nb075AlphaDummy061))).fv ∪ ((Class.cv (nb075AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0071 (x : Var) :
    (nb075AlphaDummy064 x) ∈
      (((Class.cv (nb075AlphaDummy064 x))).fv ∪ ((Class.cv (nb075AlphaDummy064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0072 :
    (nb075AlphaDummy041) ∈
      (((Class.cv (nb075AlphaDummy042))).fv ∪ ((Class.cv (nb075AlphaDummy041))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0073 :
    (nb075AlphaDummy041) ∈
      (((synCcompl (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCphi (Class.cv (nb075AlphaDummy046)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy041) ≠ (nb075AlphaDummy045) from (by
          unfold nb075AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy041) ≠ (nb075AlphaDummy046) from (by
            unfold nb075AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0074 (x : Var) :
    (nb075AlphaDummy043 x) ∈
      (((Class.cv (nb075AlphaDummy044 x))).fv ∪ ((Class.cv (nb075AlphaDummy043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0075 (x : Var) :
    (nb075AlphaDummy043 x) ∈
      (((synCcompl (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCphi (Class.cv (nb075AlphaDummy048 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy047 x) from (by
          unfold nb075AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy048 x) from (by
            unfold nb075AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0076 :
    (nb075AlphaDummy041) ∈
      (((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy045)
            (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
              (Wff.classEq (Class.cv (nb075AlphaDummy045))
                (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy041) ≠ (nb075AlphaDummy045) from (by
          unfold nb075AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy041) ≠ (nb075AlphaDummy046) from (by
            unfold nb075AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0077 (x : Var) :
    (nb075AlphaDummy043 x) ∈
      (((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb075AlphaDummy047 x)
            (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy047 x) from (by
          unfold nb075AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy048 x) from (by
            unfold nb075AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb075_support_mem_0078 :
    (nb075AlphaDummy046) ∈
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy046))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0079 (x : Var) :
    (nb075AlphaDummy048 x) ∈
      (((synCcompl (synCphi (Class.cv (nb075AlphaDummy048 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0080 :
    (nb075AlphaDummy046) ∈
      (((synCphi (Class.cv (nb075AlphaDummy046)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy046)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0081 (x : Var) :
    (nb075AlphaDummy048 x) ∈
      (((synCphi (Class.cv (nb075AlphaDummy048 x)))).fv ∪
        ((synCphi (Class.cv (nb075AlphaDummy048 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0082 :
    (nb075AlphaDummy000) ∈
      (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb075_support_mem_0083 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
