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

/-! Certificates from `NAR4C071C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_000`. -/
@[expose]
noncomputable def nb071AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_001`. -/
@[expose]
noncomputable def nb071AlphaDummy001 : Var :=
  (freshVar (({(nb071AlphaDummy000)} : Finset Var) ∪ ((synC1c)).fv ∪
      ((synCtc (synCuni (Class.cv (nb071AlphaDummy000))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_002`. -/
@[expose]
noncomputable def nb071AlphaDummy002 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synC1c)).fv ∪ ((synCtc (synCuni (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_003`. -/
@[expose]
noncomputable def nb071AlphaDummy003 : Var :=
  (freshVar
    (({(nb071AlphaDummy000)} : Finset Var) ∪ ({(nb071AlphaDummy001)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy000)) (synC1c))
          (Wff.classEq (Class.cv (nb071AlphaDummy001))
            (synCtc (synCuni (Class.cv (nb071AlphaDummy000))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_004`. -/
@[expose]
noncomputable def nb071AlphaDummy004 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb071AlphaDummy002 x)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv x) (synC1c))
          (Wff.classEq (Class.cv (nb071AlphaDummy002 x))
            (synCtc (synCuni (Class.cv x)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_005`. -/
@[expose]
noncomputable def nb071AlphaDummy005 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_006`. -/
@[expose]
noncomputable def nb071AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_007`. -/
@[expose]
noncomputable def nb071AlphaDummy007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_008`. -/
@[expose]
noncomputable def nb071AlphaDummy008 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_009`. -/
@[expose]
noncomputable def nb071AlphaDummy009 : Var :=
  (freshVar (((synCcompl (Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCphi (Class.cv (nb071AlphaDummy006)))))))).fv ∪ ((synCcompl
          (Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_010`. -/
@[expose]
noncomputable def nb071AlphaDummy010 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb071AlphaDummy007 x)
            (synWrex (nb071AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCphi (Class.cv (nb071AlphaDummy008 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb071AlphaDummy007 x)
            (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_011`. -/
@[expose]
noncomputable def nb071AlphaDummy011 : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy005)
          (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
            (Wff.classEq (Class.cv (nb071AlphaDummy005))
              (synCphi (Class.cv (nb071AlphaDummy006))))))).fv ∪
      ((Class.cab (nb071AlphaDummy005)
          (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
            (Wff.classEq (Class.cv (nb071AlphaDummy005))
              (synCphi (Class.cv (nb071AlphaDummy006))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_012`. -/
@[expose]
noncomputable def nb071AlphaDummy012 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy007 x)
          (synWrex (nb071AlphaDummy008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
              (synCphi (Class.cv (nb071AlphaDummy008 x))))))).fv ∪
      ((Class.cab (nb071AlphaDummy007 x) (synWrex (nb071AlphaDummy008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
              (synCphi (Class.cv (nb071AlphaDummy008 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_013`. -/
@[expose]
noncomputable def nb071AlphaDummy013 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_014`. -/
@[expose]
noncomputable def nb071AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy006))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_015`. -/
@[expose]
noncomputable def nb071AlphaDummy015 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy008 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_016`. -/
@[expose]
noncomputable def nb071AlphaDummy016 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy008 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_017`. -/
@[expose]
noncomputable def nb071AlphaDummy017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb071AlphaDummy013)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb071AlphaDummy013)) (synC1c))).fv ∪
      ((Class.cv (nb071AlphaDummy013))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_018`. -/
@[expose]
noncomputable def nb071AlphaDummy018 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb071AlphaDummy015 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb071AlphaDummy015 x)) (synC1c))).fv ∪
      ((Class.cv (nb071AlphaDummy015 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_019`. -/
@[expose]
noncomputable def nb071AlphaDummy019 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_020`. -/
@[expose]
noncomputable def nb071AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_021`. -/
@[expose]
noncomputable def nb071AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_022`. -/
@[expose]
noncomputable def nb071AlphaDummy022 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_023`. -/
@[expose]
noncomputable def nb071AlphaDummy023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_024`. -/
@[expose]
noncomputable def nb071AlphaDummy024 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_025`. -/
@[expose]
noncomputable def nb071AlphaDummy025 : Var :=
  (freshVar (((synCnin (Class.cv (nb071AlphaDummy020))
          (Class.cv (nb071AlphaDummy021)))).fv ∪
      ((synCnin (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_026`. -/
@[expose]
noncomputable def nb071AlphaDummy026 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb071AlphaDummy023 x))
          (Class.cv (nb071AlphaDummy024 x)))).fv ∪
      ((synCnin (Class.cv (nb071AlphaDummy023 x)) (Class.cv (nb071AlphaDummy024 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_027`. -/
@[expose]
noncomputable def nb071AlphaDummy027 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_028`. -/
@[expose]
noncomputable def nb071AlphaDummy028 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy023 x))).fv ∪
      ((Class.cv (nb071AlphaDummy024 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_029`. -/
@[expose]
noncomputable def nb071AlphaDummy029 : Var :=
  (freshVar (((synCcompl (Class.cv (nb071AlphaDummy020)))).fv ∪
      ((synCcompl (Class.cv (nb071AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_030`. -/
@[expose]
noncomputable def nb071AlphaDummy030 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb071AlphaDummy023 x)))).fv ∪
      ((synCcompl (Class.cv (nb071AlphaDummy024 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_031`. -/
@[expose]
noncomputable def nb071AlphaDummy031 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_032`. -/
@[expose]
noncomputable def nb071AlphaDummy032 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy023 x))).fv ∪
      ((Class.cv (nb071AlphaDummy023 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_033`. -/
@[expose]
noncomputable def nb071AlphaDummy033 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy021))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_034`. -/
@[expose]
noncomputable def nb071AlphaDummy034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy024 x))).fv ∪
      ((Class.cv (nb071AlphaDummy024 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_035`. -/
@[expose]
noncomputable def nb071AlphaDummy035 : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy005)
          (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
            (Wff.classEq (Class.cv (nb071AlphaDummy005))
              (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy005)
          (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
            (Wff.classEq (Class.cv (nb071AlphaDummy005))
              (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_036`. -/
@[expose]
noncomputable def nb071AlphaDummy036 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy007 x)
          (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
            (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
              (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy007 x)
          (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
            (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
              (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_037`. -/
@[expose]
noncomputable def nb071AlphaDummy037 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb071AlphaDummy006))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_038`. -/
@[expose]
noncomputable def nb071AlphaDummy038 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb071AlphaDummy008 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_039`. -/
@[expose]
noncomputable def nb071AlphaDummy039 : Var :=
  (freshVar (((synCphi (Class.cv (nb071AlphaDummy006)))).fv ∪
      ((synCphi (Class.cv (nb071AlphaDummy006)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_040`. -/
@[expose]
noncomputable def nb071AlphaDummy040 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb071AlphaDummy008 x)))).fv ∪
      ((synCphi (Class.cv (nb071AlphaDummy008 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_041`. -/
@[expose]
noncomputable def nb071AlphaDummy041 : Var :=
  (freshVar (((synCuni (Class.cv (nb071AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_042`. -/
@[expose]
noncomputable def nb071AlphaDummy042 : Var :=
  (freshVar (((synCuni (Class.cv (nb071AlphaDummy000)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_043`. -/
@[expose]
noncomputable def nb071AlphaDummy043 (x : Var) : Var :=
  (freshVar (((synCuni (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_044`. -/
@[expose]
noncomputable def nb071AlphaDummy044 (x : Var) : Var :=
  (freshVar (((synCuni (Class.cv x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_045`. -/
@[expose]
noncomputable def nb071AlphaDummy045 : Var :=
  (freshVar (({(nb071AlphaDummy041)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
          (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
            (Wff.classEq (Class.cv (nb071AlphaDummy041))
              (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_046`. -/
@[expose]
noncomputable def nb071AlphaDummy046 (x : Var) : Var :=
  (freshVar (({(nb071AlphaDummy043 x)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
          (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
            (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
              (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_047`. -/
@[expose]
noncomputable def nb071AlphaDummy047 : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy045) (Wff.classEq (Class.cab (nb071AlphaDummy041)
            (synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
              (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
                (Wff.classEq (Class.cv (nb071AlphaDummy041))
                  (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042))))))))
          (synCsn (Class.cv (nb071AlphaDummy045)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_048`. -/
@[expose]
noncomputable def nb071AlphaDummy048 : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy045) (Wff.classEq (Class.cab (nb071AlphaDummy041)
            (synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
              (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
                (Wff.classEq (Class.cv (nb071AlphaDummy041))
                  (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042))))))))
          (synCsn (Class.cv (nb071AlphaDummy045)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_049`. -/
@[expose]
noncomputable def nb071AlphaDummy049 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq
          (Class.cab (nb071AlphaDummy043 x)
            (synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
              (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
                (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                  (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))))
          (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_050`. -/
@[expose]
noncomputable def nb071AlphaDummy050 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq
          (Class.cab (nb071AlphaDummy043 x)
            (synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
              (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
                (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                  (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))))
          (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_051`. -/
@[expose]
noncomputable def nb071AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_052`. -/
@[expose]
noncomputable def nb071AlphaDummy052 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_053`. -/
@[expose]
noncomputable def nb071AlphaDummy053 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_054`. -/
@[expose]
noncomputable def nb071AlphaDummy054 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_055`. -/
@[expose]
noncomputable def nb071AlphaDummy055 : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_056`. -/
@[expose]
noncomputable def nb071AlphaDummy056 : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_057`. -/
@[expose]
noncomputable def nb071AlphaDummy057 (x : Var) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_058`. -/
@[expose]
noncomputable def nb071AlphaDummy058 (x : Var) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_059`. -/
@[expose]
noncomputable def nb071AlphaDummy059 : Var :=
  (freshVar (((synCpw1 (Class.cv (nb071AlphaDummy042)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_060`. -/
@[expose]
noncomputable def nb071AlphaDummy060 (x : Var) : Var :=
  (freshVar (((synCpw1 (Class.cv (nb071AlphaDummy044 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_061`. -/
@[expose]
noncomputable def nb071AlphaDummy061 : Var :=
  (freshVar (((synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))).fv ∪
      ((synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_062`. -/
@[expose]
noncomputable def nb071AlphaDummy062 (x : Var) : Var :=
  (freshVar (((synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))).fv ∪
      ((synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_063`. -/
@[expose]
noncomputable def nb071AlphaDummy063 : Var :=
  (freshVar (((synCpw (Class.cv (nb071AlphaDummy042)))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_064`. -/
@[expose]
noncomputable def nb071AlphaDummy064 (x : Var) : Var :=
  (freshVar (((synCpw (Class.cv (nb071AlphaDummy044 x)))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_065`. -/
@[expose]
noncomputable def nb071AlphaDummy065 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy042))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_066`. -/
@[expose]
noncomputable def nb071AlphaDummy066 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy044 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_067`. -/
@[expose]
noncomputable def nb071AlphaDummy067 : Var :=
  (freshVar (((synCnin (Class.cv (nb071AlphaDummy065))
          (Class.cv (nb071AlphaDummy042)))).fv ∪
      ((synCnin (Class.cv (nb071AlphaDummy065)) (Class.cv (nb071AlphaDummy042)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_068`. -/
@[expose]
noncomputable def nb071AlphaDummy068 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb071AlphaDummy066 x))
          (Class.cv (nb071AlphaDummy044 x)))).fv ∪
      ((synCnin (Class.cv (nb071AlphaDummy066 x)) (Class.cv (nb071AlphaDummy044 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_069`. -/
@[expose]
noncomputable def nb071AlphaDummy069 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy065))).fv ∪ ((Class.cv (nb071AlphaDummy042))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_070`. -/
@[expose]
noncomputable def nb071AlphaDummy070 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy066 x))).fv ∪
      ((Class.cv (nb071AlphaDummy044 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_071`. -/
@[expose]
noncomputable def nb071AlphaDummy071 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_072`. -/
@[expose]
noncomputable def nb071AlphaDummy072 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_073`. -/
@[expose]
noncomputable def nb071AlphaDummy073 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy058 x))).fv ∪
      ((Class.cv (nb071AlphaDummy057 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_074`. -/
@[expose]
noncomputable def nb071AlphaDummy074 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy058 x))).fv ∪
      ((Class.cv (nb071AlphaDummy057 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_075`. -/
@[expose]
noncomputable def nb071AlphaDummy075 : Var :=
  (freshVar (((synCcompl (Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCphi (Class.cv (nb071AlphaDummy072)))))))).fv ∪ ((synCcompl
          (Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_076`. -/
@[expose]
noncomputable def nb071AlphaDummy076 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCphi (Class.cv (nb071AlphaDummy074 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_077`. -/
@[expose]
noncomputable def nb071AlphaDummy077 : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy071)
          (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
            (Wff.classEq (Class.cv (nb071AlphaDummy071))
              (synCphi (Class.cv (nb071AlphaDummy072))))))).fv ∪
      ((Class.cab (nb071AlphaDummy071)
          (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
            (Wff.classEq (Class.cv (nb071AlphaDummy071))
              (synCphi (Class.cv (nb071AlphaDummy072))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_078`. -/
@[expose]
noncomputable def nb071AlphaDummy078 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy073 x)
          (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
            (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
              (synCphi (Class.cv (nb071AlphaDummy074 x))))))).fv ∪
      ((Class.cab (nb071AlphaDummy073 x)
          (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
            (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
              (synCphi (Class.cv (nb071AlphaDummy074 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_079`. -/
@[expose]
noncomputable def nb071AlphaDummy079 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy072))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_080`. -/
@[expose]
noncomputable def nb071AlphaDummy080 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy072))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_081`. -/
@[expose]
noncomputable def nb071AlphaDummy081 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy074 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_082`. -/
@[expose]
noncomputable def nb071AlphaDummy082 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy074 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_083`. -/
@[expose]
noncomputable def nb071AlphaDummy083 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb071AlphaDummy079)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb071AlphaDummy079)) (synC1c))).fv ∪
      ((Class.cv (nb071AlphaDummy079))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_084`. -/
@[expose]
noncomputable def nb071AlphaDummy084 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb071AlphaDummy081 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb071AlphaDummy081 x)) (synC1c))).fv ∪
      ((Class.cv (nb071AlphaDummy081 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_085`. -/
@[expose]
noncomputable def nb071AlphaDummy085 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_086`. -/
@[expose]
noncomputable def nb071AlphaDummy086 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_087`. -/
@[expose]
noncomputable def nb071AlphaDummy087 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_088`. -/
@[expose]
noncomputable def nb071AlphaDummy088 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_089`. -/
@[expose]
noncomputable def nb071AlphaDummy089 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_090`. -/
@[expose]
noncomputable def nb071AlphaDummy090 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_091`. -/
@[expose]
noncomputable def nb071AlphaDummy091 : Var :=
  (freshVar (((synCnin (Class.cv (nb071AlphaDummy086))
          (Class.cv (nb071AlphaDummy087)))).fv ∪
      ((synCnin (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_092`. -/
@[expose]
noncomputable def nb071AlphaDummy092 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb071AlphaDummy089 x))
          (Class.cv (nb071AlphaDummy090 x)))).fv ∪
      ((synCnin (Class.cv (nb071AlphaDummy089 x)) (Class.cv (nb071AlphaDummy090 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_093`. -/
@[expose]
noncomputable def nb071AlphaDummy093 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_094`. -/
@[expose]
noncomputable def nb071AlphaDummy094 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy089 x))).fv ∪
      ((Class.cv (nb071AlphaDummy090 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_095`. -/
@[expose]
noncomputable def nb071AlphaDummy095 : Var :=
  (freshVar (((synCcompl (Class.cv (nb071AlphaDummy086)))).fv ∪
      ((synCcompl (Class.cv (nb071AlphaDummy087)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_096`. -/
@[expose]
noncomputable def nb071AlphaDummy096 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb071AlphaDummy089 x)))).fv ∪
      ((synCcompl (Class.cv (nb071AlphaDummy090 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_097`. -/
@[expose]
noncomputable def nb071AlphaDummy097 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy086))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_098`. -/
@[expose]
noncomputable def nb071AlphaDummy098 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy089 x))).fv ∪
      ((Class.cv (nb071AlphaDummy089 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_099`. -/
@[expose]
noncomputable def nb071AlphaDummy099 : Var :=
  (freshVar
    (((Class.cv (nb071AlphaDummy087))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_100`. -/
@[expose]
noncomputable def nb071AlphaDummy100 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy090 x))).fv ∪
      ((Class.cv (nb071AlphaDummy090 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_101`. -/
@[expose]
noncomputable def nb071AlphaDummy101 : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy071)
          (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
            (Wff.classEq (Class.cv (nb071AlphaDummy071))
              (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy071)
          (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
            (Wff.classEq (Class.cv (nb071AlphaDummy071))
              (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_102`. -/
@[expose]
noncomputable def nb071AlphaDummy102 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071AlphaDummy073 x)
          (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
            (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
              (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy073 x)
          (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
            (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
              (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_103`. -/
@[expose]
noncomputable def nb071AlphaDummy103 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb071AlphaDummy072))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_104`. -/
@[expose]
noncomputable def nb071AlphaDummy104 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb071AlphaDummy074 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_105`. -/
@[expose]
noncomputable def nb071AlphaDummy105 : Var :=
  (freshVar (((synCphi (Class.cv (nb071AlphaDummy072)))).fv ∪
      ((synCphi (Class.cv (nb071AlphaDummy072)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_106`. -/
@[expose]
noncomputable def nb071AlphaDummy106 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb071AlphaDummy074 x)))).fv ∪
      ((synCphi (Class.cv (nb071AlphaDummy074 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_107`. -/
@[expose]
noncomputable def nb071AlphaDummy107 : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy045))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb071_alpha_dummy_108`. -/
@[expose]
noncomputable def nb071AlphaDummy108 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071AlphaDummy046 x))).fv) 0)

theorem nb071_fresh_000 :
    (nb071AlphaDummy011) ∉
      (((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCphi (Class.cv (nb071AlphaDummy006))))))).fv ∪
        ((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCphi (Class.cv (nb071AlphaDummy006))))))).fv) :=
  by
  simpa only [nb071AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCphi (Class.cv (nb071AlphaDummy006))))))).fv ∪
        ((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCphi (Class.cv (nb071AlphaDummy006))))))).fv)
      0

theorem nb071_fresh_001 :
    (nb071AlphaDummy035) ∉
      (((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb071AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb071_fresh_002 (x : Var) :
    (nb071AlphaDummy036 x) ∉
      (((Class.cab (nb071AlphaDummy007 x)
            (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy007 x)
            (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb071AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy007 x)
            (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy007 x)
            (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb071_fresh_003 (x : Var) :
    (nb071AlphaDummy012 x) ∉
      (((Class.cab (nb071AlphaDummy007 x) (synWrex (nb071AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCphi (Class.cv (nb071AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb071AlphaDummy007 x) (synWrex (nb071AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCphi (Class.cv (nb071AlphaDummy008 x))))))).fv) :=
  by
  simpa only [nb071AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy007 x) (synWrex (nb071AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCphi (Class.cv (nb071AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb071AlphaDummy007 x) (synWrex (nb071AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCphi (Class.cv (nb071AlphaDummy008 x))))))).fv)
      0

theorem nb071_fresh_004 :
    (nb071AlphaDummy047) ∉
      (((Class.cab (nb071AlphaDummy045) (Wff.classEq (Class.cab (nb071AlphaDummy041)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
                (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
                  (Wff.classEq (Class.cv (nb071AlphaDummy041))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042))))))))
            (synCsn (Class.cv (nb071AlphaDummy045)))))).fv) :=
  by
  simpa only [nb071AlphaDummy047] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy045) (Wff.classEq (Class.cab (nb071AlphaDummy041)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
                (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
                  (Wff.classEq (Class.cv (nb071AlphaDummy041))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042))))))))
            (synCsn (Class.cv (nb071AlphaDummy045)))))).fv)
      0

theorem nb071_fresh_005 :
    (nb071AlphaDummy048) ∉
      (((Class.cab (nb071AlphaDummy045) (Wff.classEq (Class.cab (nb071AlphaDummy041)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
                (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
                  (Wff.classEq (Class.cv (nb071AlphaDummy041))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042))))))))
            (synCsn (Class.cv (nb071AlphaDummy045)))))).fv) :=
  by
  simpa only [nb071AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy045) (Wff.classEq (Class.cab (nb071AlphaDummy041)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
                (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
                  (Wff.classEq (Class.cv (nb071AlphaDummy041))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042))))))))
            (synCsn (Class.cv (nb071AlphaDummy045)))))).fv)
      1

theorem nb071_distinct_006 : (nb071AlphaDummy047) ≠ (nb071AlphaDummy048) := by
  simpa only [nb071AlphaDummy047, nb071AlphaDummy048] using
    (freshVar_injective (((Class.cab (nb071AlphaDummy045) (Wff.classEq
            (Class.cab (nb071AlphaDummy041)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
                (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
                  (Wff.classEq (Class.cv (nb071AlphaDummy041))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042))))))))
            (synCsn (Class.cv (nb071AlphaDummy045)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_007 (x : Var) :
    (nb071AlphaDummy049 x) ∉
      (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq (Class.cab (nb071AlphaDummy043 x)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
                (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))))
            (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv) :=
  by
  simpa only [nb071AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq (Class.cab (nb071AlphaDummy043 x)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
                (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))))
            (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv)
      0

theorem nb071_fresh_008 (x : Var) :
    (nb071AlphaDummy050 x) ∉
      (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq (Class.cab (nb071AlphaDummy043 x)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
                (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))))
            (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv) :=
  by
  simpa only [nb071AlphaDummy050] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq (Class.cab (nb071AlphaDummy043 x)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
                (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))))
            (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv)
      1

theorem nb071_distinct_009 (x : Var) :
    (nb071AlphaDummy049 x) ≠ (nb071AlphaDummy050 x) := by
  simpa only [nb071AlphaDummy049, nb071AlphaDummy050] using
    (freshVar_injective (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq
            (Class.cab (nb071AlphaDummy043 x)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
                (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))))
            (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_010 :
    (nb071AlphaDummy101) ∉
      (((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb071AlphaDummy101] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb071_fresh_011 :
    (nb071AlphaDummy077) ∉
      (((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCphi (Class.cv (nb071AlphaDummy072))))))).fv ∪
        ((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCphi (Class.cv (nb071AlphaDummy072))))))).fv) :=
  by
  simpa only [nb071AlphaDummy077] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCphi (Class.cv (nb071AlphaDummy072))))))).fv ∪
        ((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCphi (Class.cv (nb071AlphaDummy072))))))).fv)
      0

theorem nb071_fresh_012 (x : Var) :
    (nb071AlphaDummy102 x) ∉
      (((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb071AlphaDummy102] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb071_fresh_013 (x : Var) :
    (nb071AlphaDummy078 x) ∉
      (((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCphi (Class.cv (nb071AlphaDummy074 x))))))).fv ∪
        ((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCphi (Class.cv (nb071AlphaDummy074 x))))))).fv) :=
  by
  simpa only [nb071AlphaDummy078] using
    freshVar_not_mem
      (((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCphi (Class.cv (nb071AlphaDummy074 x))))))).fv ∪
        ((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCphi (Class.cv (nb071AlphaDummy074 x))))))).fv)
      0

theorem nb071_fresh_014 :
    (nb071AlphaDummy051) ∉ (((Class.cv (nb071AlphaDummy000))).fv) := by
  simpa only [nb071AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy000))).fv) 0

theorem nb071_fresh_015 :
    (nb071AlphaDummy052) ∉ (((Class.cv (nb071AlphaDummy000))).fv) := by
  simpa only [nb071AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy000))).fv) 1

theorem nb071_distinct_016 : (nb071AlphaDummy051) ≠ (nb071AlphaDummy052) := by
  simpa only [nb071AlphaDummy051, nb071AlphaDummy052] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy000))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_017 :
    (nb071AlphaDummy005) ∉
      (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv) :=
  by
  simpa only [nb071AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv)
      0

theorem nb071_fresh_018 :
    (nb071AlphaDummy006) ∉
      (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv) :=
  by
  simpa only [nb071AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv)
      1

theorem nb071_distinct_019 : (nb071AlphaDummy005) ≠ (nb071AlphaDummy006) := by
  simpa only [nb071AlphaDummy005, nb071AlphaDummy006] using
    (freshVar_injective
      (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_020 :
    (nb071AlphaDummy013) ∉ (((Class.cv (nb071AlphaDummy006))).fv) := by
  simpa only [nb071AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy006))).fv) 0

theorem nb071_fresh_021 :
    (nb071AlphaDummy014) ∉ (((Class.cv (nb071AlphaDummy006))).fv) := by
  simpa only [nb071AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy006))).fv) 1

theorem nb071_distinct_022 : (nb071AlphaDummy013) ≠ (nb071AlphaDummy014) := by
  simpa only [nb071AlphaDummy013, nb071AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy006))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_023 (x : Var) :
    (nb071AlphaDummy015 x) ∉ (((Class.cv (nb071AlphaDummy008 x))).fv) := by
  simpa only [nb071AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy008 x))).fv) 0

theorem nb071_fresh_024 (x : Var) :
    (nb071AlphaDummy016 x) ∉ (((Class.cv (nb071AlphaDummy008 x))).fv) := by
  simpa only [nb071AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy008 x))).fv) 1

theorem nb071_distinct_025 (x : Var) :
    (nb071AlphaDummy015 x) ≠ (nb071AlphaDummy016 x) := by
  simpa only [nb071AlphaDummy015, nb071AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy008 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb071_fresh_026 :
    (nb071AlphaDummy019) ∉
      (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) 0

theorem nb071_fresh_027 :
    (nb071AlphaDummy020) ∉
      (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) 1

theorem nb071_fresh_028 :
    (nb071AlphaDummy021) ∉
      (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) 2

theorem nb071_distinct_029 : (nb071AlphaDummy019) ≠ (nb071AlphaDummy020) := by
  simpa only [nb071AlphaDummy019, nb071AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb071_distinct_030 : (nb071AlphaDummy019) ≠ (nb071AlphaDummy021) := by
  simpa only [nb071AlphaDummy019, nb071AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb071_distinct_031 : (nb071AlphaDummy020) ≠ (nb071AlphaDummy021) := by
  simpa only [nb071AlphaDummy020, nb071AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb071_fresh_032 (x : Var) :
    (nb071AlphaDummy022 x) ∉
      (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 0

theorem nb071_fresh_033 (x : Var) :
    (nb071AlphaDummy023 x) ∉
      (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 1

theorem nb071_fresh_034 (x : Var) :
    (nb071AlphaDummy024 x) ∉
      (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 2

theorem nb071_distinct_035 (x : Var) :
    (nb071AlphaDummy022 x) ≠ (nb071AlphaDummy023 x) := by
  simpa only [nb071AlphaDummy022, nb071AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb071_distinct_036 (x : Var) :
    (nb071AlphaDummy022 x) ≠ (nb071AlphaDummy024 x) := by
  simpa only [nb071AlphaDummy022, nb071AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb071_distinct_037 (x : Var) :
    (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy024 x) := by
  simpa only [nb071AlphaDummy023, nb071AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb071_fresh_038 :
    (nb071AlphaDummy031) ∉
      (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy020))).fv) :=
  by
  simpa only [nb071AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy020))).fv)
      0

theorem nb071_fresh_039 :
    (nb071AlphaDummy027) ∉
      (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv) :=
  by
  simpa only [nb071AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv)
      0

theorem nb071_fresh_040 :
    (nb071AlphaDummy033) ∉
      (((Class.cv (nb071AlphaDummy021))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv) :=
  by
  simpa only [nb071AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy021))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C071C001Part002`. -/


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

theorem nb071_fresh_041 (x : Var) :
    (nb071AlphaDummy032 x) ∉
      (((Class.cv (nb071AlphaDummy023 x))).fv ∪ ((Class.cv (nb071AlphaDummy023 x))).fv) :=
  by
  simpa only [nb071AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy023 x))).fv ∪ ((Class.cv (nb071AlphaDummy023 x))).fv)
      0

theorem nb071_fresh_042 (x : Var) :
    (nb071AlphaDummy028 x) ∉
      (((Class.cv (nb071AlphaDummy023 x))).fv ∪ ((Class.cv (nb071AlphaDummy024 x))).fv) :=
  by
  simpa only [nb071AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy023 x))).fv ∪ ((Class.cv (nb071AlphaDummy024 x))).fv)
      0

theorem nb071_fresh_043 (x : Var) :
    (nb071AlphaDummy034 x) ∉
      (((Class.cv (nb071AlphaDummy024 x))).fv ∪ ((Class.cv (nb071AlphaDummy024 x))).fv) :=
  by
  simpa only [nb071AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy024 x))).fv ∪ ((Class.cv (nb071AlphaDummy024 x))).fv)
      0

theorem nb071_fresh_044 :
    (nb071AlphaDummy065) ∉ (((Class.cv (nb071AlphaDummy042))).fv) := by
  simpa only [nb071AlphaDummy065] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy042))).fv) 0

theorem nb071_fresh_045 (x : Var) :
    (nb071AlphaDummy066 x) ∉ (((Class.cv (nb071AlphaDummy044 x))).fv) := by
  simpa only [nb071AlphaDummy066] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy044 x))).fv) 0

theorem nb071_fresh_046 :
    (nb071AlphaDummy107) ∉ (((Class.cv (nb071AlphaDummy045))).fv) := by
  simpa only [nb071AlphaDummy107] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy045))).fv) 0

theorem nb071_fresh_047 (x : Var) :
    (nb071AlphaDummy108 x) ∉ (((Class.cv (nb071AlphaDummy046 x))).fv) := by
  simpa only [nb071AlphaDummy108] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy046 x))).fv) 0

theorem nb071_fresh_048 :
    (nb071AlphaDummy071) ∉
      (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv) :=
  by
  simpa only [nb071AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv)
      0

theorem nb071_fresh_049 :
    (nb071AlphaDummy072) ∉
      (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv) :=
  by
  simpa only [nb071AlphaDummy072] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv)
      1

theorem nb071_distinct_050 : (nb071AlphaDummy071) ≠ (nb071AlphaDummy072) := by
  simpa only [nb071AlphaDummy071, nb071AlphaDummy072] using
    (freshVar_injective
      (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_051 (x : Var) :
    (nb071AlphaDummy073 x) ∉
      (((Class.cv (nb071AlphaDummy058 x))).fv ∪ ((Class.cv (nb071AlphaDummy057 x))).fv) :=
  by
  simpa only [nb071AlphaDummy073] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy058 x))).fv ∪ ((Class.cv (nb071AlphaDummy057 x))).fv)
      0

theorem nb071_fresh_052 (x : Var) :
    (nb071AlphaDummy074 x) ∉
      (((Class.cv (nb071AlphaDummy058 x))).fv ∪ ((Class.cv (nb071AlphaDummy057 x))).fv) :=
  by
  simpa only [nb071AlphaDummy074] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy058 x))).fv ∪ ((Class.cv (nb071AlphaDummy057 x))).fv)
      1

theorem nb071_distinct_053 (x : Var) :
    (nb071AlphaDummy073 x) ≠ (nb071AlphaDummy074 x) := by
  simpa only [nb071AlphaDummy073, nb071AlphaDummy074] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy058 x))).fv ∪
        ((Class.cv (nb071AlphaDummy057 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_054 :
    (nb071AlphaDummy069) ∉
      (((Class.cv (nb071AlphaDummy065))).fv ∪ ((Class.cv (nb071AlphaDummy042))).fv) :=
  by
  simpa only [nb071AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy065))).fv ∪ ((Class.cv (nb071AlphaDummy042))).fv)
      0

theorem nb071_fresh_055 (x : Var) :
    (nb071AlphaDummy070 x) ∉
      (((Class.cv (nb071AlphaDummy066 x))).fv ∪ ((Class.cv (nb071AlphaDummy044 x))).fv) :=
  by
  simpa only [nb071AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy066 x))).fv ∪ ((Class.cv (nb071AlphaDummy044 x))).fv)
      0

theorem nb071_fresh_056 :
    (nb071AlphaDummy079) ∉ (((Class.cv (nb071AlphaDummy072))).fv) := by
  simpa only [nb071AlphaDummy079] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy072))).fv) 0

theorem nb071_fresh_057 :
    (nb071AlphaDummy080) ∉ (((Class.cv (nb071AlphaDummy072))).fv) := by
  simpa only [nb071AlphaDummy080] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy072))).fv) 1

theorem nb071_distinct_058 : (nb071AlphaDummy079) ≠ (nb071AlphaDummy080) := by
  simpa only [nb071AlphaDummy079, nb071AlphaDummy080] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy072))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_059 (x : Var) :
    (nb071AlphaDummy081 x) ∉ (((Class.cv (nb071AlphaDummy074 x))).fv) := by
  simpa only [nb071AlphaDummy081] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy074 x))).fv) 0

theorem nb071_fresh_060 (x : Var) :
    (nb071AlphaDummy082 x) ∉ (((Class.cv (nb071AlphaDummy074 x))).fv) := by
  simpa only [nb071AlphaDummy082] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy074 x))).fv) 1

theorem nb071_distinct_061 (x : Var) :
    (nb071AlphaDummy081 x) ≠ (nb071AlphaDummy082 x) := by
  simpa only [nb071AlphaDummy081, nb071AlphaDummy082] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy074 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb071_fresh_062 :
    (nb071AlphaDummy085) ∉
      (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy085] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) 0

theorem nb071_fresh_063 :
    (nb071AlphaDummy086) ∉
      (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy086] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) 1

theorem nb071_fresh_064 :
    (nb071AlphaDummy087) ∉
      (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy087] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) 2

theorem nb071_distinct_065 : (nb071AlphaDummy085) ≠ (nb071AlphaDummy086) := by
  simpa only [nb071AlphaDummy085, nb071AlphaDummy086] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb071_distinct_066 : (nb071AlphaDummy085) ≠ (nb071AlphaDummy087) := by
  simpa only [nb071AlphaDummy085, nb071AlphaDummy087] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb071_distinct_067 : (nb071AlphaDummy086) ≠ (nb071AlphaDummy087) := by
  simpa only [nb071AlphaDummy086, nb071AlphaDummy087] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb071_fresh_068 (x : Var) :
    (nb071AlphaDummy088 x) ∉
      (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy088] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) 0

theorem nb071_fresh_069 (x : Var) :
    (nb071AlphaDummy089 x) ∉
      (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy089] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) 1

theorem nb071_fresh_070 (x : Var) :
    (nb071AlphaDummy090 x) ∉
      (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy090] using
    freshVar_not_mem (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) 2

theorem nb071_distinct_071 (x : Var) :
    (nb071AlphaDummy088 x) ≠ (nb071AlphaDummy089 x) := by
  simpa only [nb071AlphaDummy088, nb071AlphaDummy089] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb071_distinct_072 (x : Var) :
    (nb071AlphaDummy088 x) ≠ (nb071AlphaDummy090 x) := by
  simpa only [nb071AlphaDummy088, nb071AlphaDummy090] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb071_distinct_073 (x : Var) :
    (nb071AlphaDummy089 x) ≠ (nb071AlphaDummy090 x) := by
  simpa only [nb071AlphaDummy089, nb071AlphaDummy090] using
    (freshVar_injective (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb071_fresh_074 :
    (nb071AlphaDummy097) ∉
      (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy086))).fv) :=
  by
  simpa only [nb071AlphaDummy097] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy086))).fv)
      0

theorem nb071_fresh_075 :
    (nb071AlphaDummy093) ∉
      (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv) :=
  by
  simpa only [nb071AlphaDummy093] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv)
      0

theorem nb071_fresh_076 :
    (nb071AlphaDummy099) ∉
      (((Class.cv (nb071AlphaDummy087))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv) :=
  by
  simpa only [nb071AlphaDummy099] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy087))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv)
      0

theorem nb071_fresh_077 (x : Var) :
    (nb071AlphaDummy098 x) ∉
      (((Class.cv (nb071AlphaDummy089 x))).fv ∪ ((Class.cv (nb071AlphaDummy089 x))).fv) :=
  by
  simpa only [nb071AlphaDummy098] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy089 x))).fv ∪ ((Class.cv (nb071AlphaDummy089 x))).fv)
      0

theorem nb071_fresh_078 (x : Var) :
    (nb071AlphaDummy094 x) ∉
      (((Class.cv (nb071AlphaDummy089 x))).fv ∪ ((Class.cv (nb071AlphaDummy090 x))).fv) :=
  by
  simpa only [nb071AlphaDummy094] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy089 x))).fv ∪ ((Class.cv (nb071AlphaDummy090 x))).fv)
      0

theorem nb071_fresh_079 (x : Var) :
    (nb071AlphaDummy100 x) ∉
      (((Class.cv (nb071AlphaDummy090 x))).fv ∪ ((Class.cv (nb071AlphaDummy090 x))).fv) :=
  by
  simpa only [nb071AlphaDummy100] using
    freshVar_not_mem
      (((Class.cv (nb071AlphaDummy090 x))).fv ∪ ((Class.cv (nb071AlphaDummy090 x))).fv)
      0

theorem nb071_fresh_080 (x : Var) : (nb071AlphaDummy053 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb071AlphaDummy053] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb071_fresh_081 (x : Var) : (nb071AlphaDummy054 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb071AlphaDummy054] using freshVar_not_mem (((Class.cv x)).fv) 1

theorem nb071_distinct_082 (x : Var) :
    (nb071AlphaDummy053 x) ≠ (nb071AlphaDummy054 x) := by
  simpa only [nb071AlphaDummy053, nb071AlphaDummy054] using
    (freshVar_injective (((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_083 (x : Var) :
    (nb071AlphaDummy007 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) :=
  by
  simpa only [nb071AlphaDummy007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) 0

theorem nb071_fresh_084 (x : Var) :
    (nb071AlphaDummy008 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) :=
  by
  simpa only [nb071AlphaDummy008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) 1

theorem nb071_distinct_085 (x : Var) :
    (nb071AlphaDummy007 x) ≠ (nb071AlphaDummy008 x) := by
  simpa only [nb071AlphaDummy007, nb071AlphaDummy008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_086 :
    (nb071AlphaDummy017) ∉
      (((Wff.classMem (Class.cv (nb071AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy013))).fv) :=
  by
  simpa only [nb071AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb071AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy013))).fv)
      0

theorem nb071_fresh_087 (x : Var) :
    (nb071AlphaDummy018 x) ∉
      (((Wff.classMem (Class.cv (nb071AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy015 x))).fv) :=
  by
  simpa only [nb071AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb071AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy015 x))).fv)
      0

theorem nb071_fresh_088 :
    (nb071AlphaDummy083) ∉
      (((Wff.classMem (Class.cv (nb071AlphaDummy079)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy079)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy079))).fv) :=
  by
  simpa only [nb071AlphaDummy083] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb071AlphaDummy079)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy079)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy079))).fv)
      0

theorem nb071_fresh_089 (x : Var) :
    (nb071AlphaDummy084 x) ∉
      (((Wff.classMem (Class.cv (nb071AlphaDummy081 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy081 x)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy081 x))).fv) :=
  by
  simpa only [nb071AlphaDummy084] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb071AlphaDummy081 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy081 x)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy081 x))).fv)
      0

theorem nb071_fresh_090 :
    (nb071AlphaDummy009) ∉
      (((synCcompl (Class.cab (nb071AlphaDummy005)
              (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
                (Wff.classEq (Class.cv (nb071AlphaDummy005))
                  (synCphi (Class.cv (nb071AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy005)
              (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
                (Wff.classEq (Class.cv (nb071AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb071AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb071AlphaDummy005)
              (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
                (Wff.classEq (Class.cv (nb071AlphaDummy005))
                  (synCphi (Class.cv (nb071AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy005)
              (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
                (Wff.classEq (Class.cv (nb071AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb071_fresh_091 (x : Var) :
    (nb071AlphaDummy010 x) ∉
      (((synCcompl (Class.cab (nb071AlphaDummy007 x)
              (synWrex (nb071AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                  (synCphi (Class.cv (nb071AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy007 x)
              (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb071AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb071AlphaDummy007 x)
              (synWrex (nb071AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                  (synCphi (Class.cv (nb071AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy007 x)
              (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb071_fresh_092 :
    (nb071AlphaDummy075) ∉
      (((synCcompl (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCphi (Class.cv (nb071AlphaDummy072)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb071AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCphi (Class.cv (nb071AlphaDummy072)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb071_fresh_093 (x : Var) :
    (nb071AlphaDummy076 x) ∉
      (((synCcompl (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCphi (Class.cv (nb071AlphaDummy074 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb071AlphaDummy076] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCphi (Class.cv (nb071AlphaDummy074 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb071_fresh_094 :
    (nb071AlphaDummy029) ∉
      (((synCcompl (Class.cv (nb071AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy021)))).fv) :=
  by
  simpa only [nb071AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb071AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy021)))).fv)
      0

theorem nb071_fresh_095 (x : Var) :
    (nb071AlphaDummy030 x) ∉
      (((synCcompl (Class.cv (nb071AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy024 x)))).fv) :=
  by
  simpa only [nb071AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb071AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy024 x)))).fv)
      0

theorem nb071_fresh_096 :
    (nb071AlphaDummy095) ∉
      (((synCcompl (Class.cv (nb071AlphaDummy086)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy087)))).fv) :=
  by
  simpa only [nb071AlphaDummy095] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb071AlphaDummy086)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy087)))).fv)
      0

theorem nb071_fresh_097 (x : Var) :
    (nb071AlphaDummy096 x) ∉
      (((synCcompl (Class.cv (nb071AlphaDummy089 x)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy090 x)))).fv) :=
  by
  simpa only [nb071AlphaDummy096] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb071AlphaDummy089 x)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy090 x)))).fv)
      0

theorem nb071_fresh_098 :
    (nb071AlphaDummy037) ∉
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb071AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb071_fresh_099 (x : Var) :
    (nb071AlphaDummy038 x) ∉
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb071AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb071_fresh_100 :
    (nb071AlphaDummy103) ∉
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy072))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb071AlphaDummy103] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy072))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb071_fresh_101 (x : Var) :
    (nb071AlphaDummy104 x) ∉
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy074 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb071AlphaDummy104] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy074 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb071_fresh_102 :
    (nb071AlphaDummy055) ∉
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv) :=
  by
  simpa only [nb071AlphaDummy055] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv) 0

theorem nb071_fresh_103 :
    (nb071AlphaDummy056) ∉
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv) :=
  by
  simpa only [nb071AlphaDummy056] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv) 1

theorem nb071_distinct_104 : (nb071AlphaDummy055) ≠ (nb071AlphaDummy056) := by
  simpa only [nb071AlphaDummy055, nb071AlphaDummy056] using
    (freshVar_injective
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_105 (x : Var) :
    (nb071AlphaDummy057 x) ∉
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv) :=
  by
  simpa only [nb071AlphaDummy057] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv) 0

theorem nb071_fresh_106 (x : Var) :
    (nb071AlphaDummy058 x) ∉
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv) :=
  by
  simpa only [nb071AlphaDummy058] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv) 1

theorem nb071_distinct_107 (x : Var) :
    (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy058 x) := by
  simpa only [nb071AlphaDummy057, nb071AlphaDummy058] using
    (freshVar_injective
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_108 :
    (nb071AlphaDummy025) ∉
      (((synCnin (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy020))
            (Class.cv (nb071AlphaDummy021)))).fv) :=
  by
  simpa only [nb071AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021)))).fv)
      0

theorem nb071_fresh_109 (x : Var) :
    (nb071AlphaDummy026 x) ∉
      (((synCnin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x)))).fv) :=
  by
  simpa only [nb071AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x)))).fv)
      0

theorem nb071_fresh_110 :
    (nb071AlphaDummy067) ∉
      (((synCnin (Class.cv (nb071AlphaDummy065)) (Class.cv (nb071AlphaDummy042)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy065))
            (Class.cv (nb071AlphaDummy042)))).fv) :=
  by
  simpa only [nb071AlphaDummy067] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb071AlphaDummy065)) (Class.cv (nb071AlphaDummy042)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy065)) (Class.cv (nb071AlphaDummy042)))).fv)
      0

theorem nb071_fresh_111 (x : Var) :
    (nb071AlphaDummy068 x) ∉
      (((synCnin (Class.cv (nb071AlphaDummy066 x))
            (Class.cv (nb071AlphaDummy044 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy066 x))
            (Class.cv (nb071AlphaDummy044 x)))).fv) :=
  by
  simpa only [nb071AlphaDummy068] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb071AlphaDummy066 x))
            (Class.cv (nb071AlphaDummy044 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy066 x))
            (Class.cv (nb071AlphaDummy044 x)))).fv)
      0

theorem nb071_fresh_112 :
    (nb071AlphaDummy091) ∉
      (((synCnin (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy086))
            (Class.cv (nb071AlphaDummy087)))).fv) :=
  by
  simpa only [nb071AlphaDummy091] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087)))).fv)
      0

theorem nb071_fresh_113 (x : Var) :
    (nb071AlphaDummy092 x) ∉
      (((synCnin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x)))).fv) :=
  by
  simpa only [nb071AlphaDummy092] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x)))).fv)
      0

theorem nb071_fresh_114 :
    (nb071AlphaDummy061) ∉
      (((synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))).fv) :=
  by
  simpa only [nb071AlphaDummy061] using
    freshVar_not_mem
      (((synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))).fv)
      0

theorem nb071_fresh_115 (x : Var) :
    (nb071AlphaDummy062 x) ∉
      (((synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))).fv) :=
  by
  simpa only [nb071AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))).fv)
      0

theorem nb071_fresh_116 :
    (nb071AlphaDummy039) ∉
      (((synCphi (Class.cv (nb071AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy006)))).fv) :=
  by
  simpa only [nb071AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb071AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy006)))).fv)
      0

theorem nb071_fresh_117 (x : Var) :
    (nb071AlphaDummy040 x) ∉
      (((synCphi (Class.cv (nb071AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy008 x)))).fv) :=
  by
  simpa only [nb071AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb071AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy008 x)))).fv)
      0

theorem nb071_fresh_118 :
    (nb071AlphaDummy105) ∉
      (((synCphi (Class.cv (nb071AlphaDummy072)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy072)))).fv) :=
  by
  simpa only [nb071AlphaDummy105] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb071AlphaDummy072)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy072)))).fv)
      0

theorem nb071_fresh_119 (x : Var) :
    (nb071AlphaDummy106 x) ∉
      (((synCphi (Class.cv (nb071AlphaDummy074 x)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy074 x)))).fv) :=
  by
  simpa only [nb071AlphaDummy106] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb071AlphaDummy074 x)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy074 x)))).fv)
      0

theorem nb071_fresh_120 :
    (nb071AlphaDummy063) ∉
      (((synCpw (Class.cv (nb071AlphaDummy042)))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy063] using
    freshVar_not_mem (((synCpw (Class.cv (nb071AlphaDummy042)))).fv ∪ ((synC1c)).fv)
      0

theorem nb071_fresh_121 (x : Var) :
    (nb071AlphaDummy064 x) ∉
      (((synCpw (Class.cv (nb071AlphaDummy044 x)))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb071AlphaDummy064] using
    freshVar_not_mem
      (((synCpw (Class.cv (nb071AlphaDummy044 x)))).fv ∪ ((synC1c)).fv) 0

theorem nb071_fresh_122 :
    (nb071AlphaDummy059) ∉ (((synCpw1 (Class.cv (nb071AlphaDummy042)))).fv) := by
  simpa only [nb071AlphaDummy059] using
    freshVar_not_mem (((synCpw1 (Class.cv (nb071AlphaDummy042)))).fv) 0

theorem nb071_fresh_123 (x : Var) :
    (nb071AlphaDummy060 x) ∉ (((synCpw1 (Class.cv (nb071AlphaDummy044 x)))).fv) :=
  by
  simpa only [nb071AlphaDummy060] using
    freshVar_not_mem (((synCpw1 (Class.cv (nb071AlphaDummy044 x)))).fv) 0

theorem nb071_fresh_124 :
    (nb071AlphaDummy041) ∉ (((synCuni (Class.cv (nb071AlphaDummy000)))).fv) := by
  simpa only [nb071AlphaDummy041] using
    freshVar_not_mem (((synCuni (Class.cv (nb071AlphaDummy000)))).fv) 0

theorem nb071_fresh_125 :
    (nb071AlphaDummy042) ∉ (((synCuni (Class.cv (nb071AlphaDummy000)))).fv) := by
  simpa only [nb071AlphaDummy042] using
    freshVar_not_mem (((synCuni (Class.cv (nb071AlphaDummy000)))).fv) 1

theorem nb071_distinct_126 : (nb071AlphaDummy041) ≠ (nb071AlphaDummy042) := by
  simpa only [nb071AlphaDummy041, nb071AlphaDummy042] using
    (freshVar_injective (((synCuni (Class.cv (nb071AlphaDummy000)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb071_fresh_127 (x : Var) :
    (nb071AlphaDummy043 x) ∉ (((synCuni (Class.cv x))).fv) := by
  simpa only [nb071AlphaDummy043] using
    freshVar_not_mem (((synCuni (Class.cv x))).fv) 0

theorem nb071_fresh_128 (x : Var) :
    (nb071AlphaDummy044 x) ∉ (((synCuni (Class.cv x))).fv) := by
  simpa only [nb071AlphaDummy044] using
    freshVar_not_mem (((synCuni (Class.cv x))).fv) 1

theorem nb071_distinct_129 (x : Var) :
    (nb071AlphaDummy043 x) ≠ (nb071AlphaDummy044 x) := by
  simpa only [nb071AlphaDummy043, nb071AlphaDummy044] using
    (freshVar_injective (((synCuni (Class.cv x))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_130 :
    (nb071AlphaDummy001) ∉
      (({(nb071AlphaDummy000)} : Finset Var) ∪ ((synC1c)).fv ∪
        ((synCtc (synCuni (Class.cv (nb071AlphaDummy000))))).fv) :=
  by
  simpa only [nb071AlphaDummy001] using
    freshVar_not_mem
      (({(nb071AlphaDummy000)} : Finset Var) ∪ ((synC1c)).fv ∪
        ((synCtc (synCuni (Class.cv (nb071AlphaDummy000))))).fv)
      0

theorem nb071_fresh_131 :
    (nb071AlphaDummy003) ∉
      (({(nb071AlphaDummy000)} : Finset Var) ∪ ({(nb071AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy000)) (synC1c))
            (Wff.classEq (Class.cv (nb071AlphaDummy001))
              (synCtc (synCuni (Class.cv (nb071AlphaDummy000))))))).fv) :=
  by
  simpa only [nb071AlphaDummy003] using
    freshVar_not_mem
      (({(nb071AlphaDummy000)} : Finset Var) ∪ ({(nb071AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy000)) (synC1c))
            (Wff.classEq (Class.cv (nb071AlphaDummy001))
              (synCtc (synCuni (Class.cv (nb071AlphaDummy000))))))).fv)
      0

theorem nb071_fresh_132 :
    (nb071AlphaDummy045) ∉
      (({(nb071AlphaDummy041)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
            (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
              (Wff.classEq (Class.cv (nb071AlphaDummy041))
                (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042)))))))).fv) :=
  by
  simpa only [nb071AlphaDummy045] using
    freshVar_not_mem
      (({(nb071AlphaDummy041)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
            (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
              (Wff.classEq (Class.cv (nb071AlphaDummy041))
                (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042)))))))).fv)
      0

theorem nb071_fresh_133 (x : Var) :
    (nb071AlphaDummy046 x) ∉
      (({(nb071AlphaDummy043 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
            (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
              (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x)))))))).fv) :=
  by
  simpa only [nb071AlphaDummy046] using
    freshVar_not_mem
      (({(nb071AlphaDummy043 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
            (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
              (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x)))))))).fv)
      0

theorem nb071_fresh_134 (x : Var) :
    (nb071AlphaDummy002 x) ∉
      (({ x } : Finset Var) ∪ ((synC1c)).fv ∪ ((synCtc (synCuni (Class.cv x)))).fv) :=
  by
  simpa only [nb071AlphaDummy002] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synC1c)).fv ∪ ((synCtc (synCuni (Class.cv x)))).fv) 0

theorem nb071_fresh_135 (x : Var) :
    (nb071AlphaDummy004 x) ∉
      (({ x } : Finset Var) ∪ ({(nb071AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synC1c))
            (Wff.classEq (Class.cv (nb071AlphaDummy002 x))
              (synCtc (synCuni (Class.cv x)))))).fv) :=
  by
  simpa only [nb071AlphaDummy004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb071AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synC1c))
            (Wff.classEq (Class.cv (nb071AlphaDummy002 x))
              (synCtc (synCuni (Class.cv x)))))).fv)
      0

theorem nb071_fresh_136 : (nb071AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb071AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb071_support_mem_0000 :
    (nb071AlphaDummy000) ∈
      (({(nb071AlphaDummy000)} : Finset Var) ∪ ({(nb071AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy000)) (synC1c))
            (Wff.classEq (Class.cv (nb071AlphaDummy001))
              (synCtc (synCuni (Class.cv (nb071AlphaDummy000))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0001 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb071AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synC1c))
            (Wff.classEq (Class.cv (nb071AlphaDummy002 x))
              (synCtc (synCuni (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0002 :
    (nb071AlphaDummy001) ∈
      (({(nb071AlphaDummy000)} : Finset Var) ∪ ({(nb071AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy000)) (synC1c))
            (Wff.classEq (Class.cv (nb071AlphaDummy001))
              (synCtc (synCuni (Class.cv (nb071AlphaDummy000))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0003 (x : Var) :
    (nb071AlphaDummy002 x) ∈
      (({ x } : Finset Var) ∪ ({(nb071AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synC1c))
            (Wff.classEq (Class.cv (nb071AlphaDummy002 x))
              (synCtc (synCuni (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0004 :
    (nb071AlphaDummy000) ∈
      (({(nb071AlphaDummy000)} : Finset Var) ∪ ((synC1c)).fv ∪
        ((synCtc (synCuni (Class.cv (nb071AlphaDummy000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0005 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synC1c)).fv ∪ ((synCtc (synCuni (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0006 :
    (nb071AlphaDummy000) ∈
      (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0007 :
    (nb071AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb071AlphaDummy005)
              (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
                (Wff.classEq (Class.cv (nb071AlphaDummy005))
                  (synCphi (Class.cv (nb071AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy005)
              (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
                (Wff.classEq (Class.cv (nb071AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy005) from (by
          unfold nb071AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy006) from (by
            unfold nb071AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0008 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0009 (x : Var) :
    x ∈
      (((synCcompl (Class.cab (nb071AlphaDummy007 x)
              (synWrex (nb071AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                  (synCphi (Class.cv (nb071AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy007 x)
              (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb071AlphaDummy007 x) from (by
          unfold nb071AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb071AlphaDummy008 x) from (by
            unfold nb071AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0010 :
    (nb071AlphaDummy000) ∈
      (((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCphi (Class.cv (nb071AlphaDummy006))))))).fv ∪
        ((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCphi (Class.cv (nb071AlphaDummy006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy005) from (by
          unfold nb071AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy006) from (by
            unfold nb071AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0011 (x : Var) :
    x ∈
      (((Class.cab (nb071AlphaDummy007 x) (synWrex (nb071AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCphi (Class.cv (nb071AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb071AlphaDummy007 x) (synWrex (nb071AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCphi (Class.cv (nb071AlphaDummy008 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb071AlphaDummy007 x) from (by
          unfold nb071AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb071AlphaDummy008 x) from (by
            unfold nb071AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0012 :
    (nb071AlphaDummy006) ∈ (((Class.cv (nb071AlphaDummy006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0013 (x : Var) :
    (nb071AlphaDummy008 x) ∈ (((Class.cv (nb071AlphaDummy008 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0014 :
    (nb071AlphaDummy013) ∈
      (((Wff.classMem (Class.cv (nb071AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy013))).fv) :=
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

theorem nb071_support_mem_0015 (x : Var) :
    (nb071AlphaDummy015 x) ∈
      (((Wff.classMem (Class.cv (nb071AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy015 x))).fv) :=
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

theorem nb071_support_mem_0016 :
    (nb071AlphaDummy013) ∈
      (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0017 (x : Var) :
    (nb071AlphaDummy015 x) ∈
      (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0018 :
    (nb071AlphaDummy020) ∈
      (((synCnin (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy020))
            (Class.cv (nb071AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0019 (x : Var) :
    (nb071AlphaDummy023 x) ∈
      (((synCnin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0020 :
    (nb071AlphaDummy020) ∈
      (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0021 (x : Var) :
    (nb071AlphaDummy023 x) ∈
      (((Class.cv (nb071AlphaDummy023 x))).fv ∪ ((Class.cv (nb071AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0022 :
    (nb071AlphaDummy021) ∈
      (((synCnin (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy020))
            (Class.cv (nb071AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0023 (x : Var) :
    (nb071AlphaDummy024 x) ∈
      (((synCnin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0024 :
    (nb071AlphaDummy021) ∈
      (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0025 (x : Var) :
    (nb071AlphaDummy024 x) ∈
      (((Class.cv (nb071AlphaDummy023 x))).fv ∪ ((Class.cv (nb071AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0026 :
    (nb071AlphaDummy020) ∈
      (((synCcompl (Class.cv (nb071AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0027 (x : Var) :
    (nb071AlphaDummy023 x) ∈
      (((synCcompl (Class.cv (nb071AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0028 :
    (nb071AlphaDummy020) ∈
      (((Class.cv (nb071AlphaDummy020))).fv ∪ ((Class.cv (nb071AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0029 (x : Var) :
    (nb071AlphaDummy023 x) ∈
      (((Class.cv (nb071AlphaDummy023 x))).fv ∪ ((Class.cv (nb071AlphaDummy023 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0030 :
    (nb071AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb071AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0031 (x : Var) :
    (nb071AlphaDummy024 x) ∈
      (((synCcompl (Class.cv (nb071AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0032 :
    (nb071AlphaDummy021) ∈
      (((Class.cv (nb071AlphaDummy021))).fv ∪ ((Class.cv (nb071AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0033 (x : Var) :
    (nb071AlphaDummy024 x) ∈
      (((Class.cv (nb071AlphaDummy024 x))).fv ∪ ((Class.cv (nb071AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0034 :
    (nb071AlphaDummy001) ∈
      (((Class.cv (nb071AlphaDummy000))).fv ∪ ((Class.cv (nb071AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0035 :
    (nb071AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb071AlphaDummy005)
              (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy000))
                (Wff.classEq (Class.cv (nb071AlphaDummy005))
                  (synCphi (Class.cv (nb071AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy005)
              (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
                (Wff.classEq (Class.cv (nb071AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy005) from (by
          unfold nb071AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy006) from (by
            unfold nb071AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0036 (x : Var) :
    (nb071AlphaDummy002 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0037 (x : Var) :
    (nb071AlphaDummy002 x) ∈
      (((synCcompl (Class.cab (nb071AlphaDummy007 x)
              (synWrex (nb071AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                  (synCphi (Class.cv (nb071AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy007 x)
              (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy007 x) from (by
          unfold nb071AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy008 x) from (by
            unfold nb071AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0038 :
    (nb071AlphaDummy001) ∈
      (((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy005)
            (synWrex (nb071AlphaDummy006) (Class.cv (nb071AlphaDummy001))
              (Wff.classEq (Class.cv (nb071AlphaDummy005))
                (synCun (synCphi (Class.cv (nb071AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy005) from (by
          unfold nb071AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy006) from (by
            unfold nb071AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0039 (x : Var) :
    (nb071AlphaDummy002 x) ∈
      (((Class.cab (nb071AlphaDummy007 x)
            (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy007 x)
            (synWrex (nb071AlphaDummy008 x) (Class.cv (nb071AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy007 x) from (by
          unfold nb071AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy008 x) from (by
            unfold nb071AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0040 :
    (nb071AlphaDummy006) ∈
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0041 (x : Var) :
    (nb071AlphaDummy008 x) ∈
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0042 :
    (nb071AlphaDummy006) ∈
      (((synCphi (Class.cv (nb071AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0043 (x : Var) :
    (nb071AlphaDummy008 x) ∈
      (((synCphi (Class.cv (nb071AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy008 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0044 :
    (nb071AlphaDummy000) ∈ (((synCuni (Class.cv (nb071AlphaDummy000)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0045 :
    (nb071AlphaDummy000) ∈
      (({(nb071AlphaDummy041)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
            (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
              (Wff.classEq (Class.cv (nb071AlphaDummy041))
                (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wrex]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy042) from (by
          unfold nb071AlphaDummy042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0044) 1))))
  · rw [fv_syn_cuni]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb071_support_mem_0046 :
    (nb071AlphaDummy000) ∈
      (((Class.cab (nb071AlphaDummy045) (Wff.classEq (Class.cab (nb071AlphaDummy041)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy041)) (synCncs))
                (synWrex (nb071AlphaDummy042) (synCuni (Class.cv (nb071AlphaDummy000)))
                  (Wff.classEq (Class.cv (nb071AlphaDummy041))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042))))))))
            (synCsn (Class.cv (nb071AlphaDummy045)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy045) from (by
          unfold nb071AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0045) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy041) from (by
            unfold nb071AlphaDummy041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0044) 0))))
    · rw [fv_syn_wa]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact
          (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy042) from (by
              unfold nb071AlphaDummy042;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0044) 1))))
      · rw [fv_syn_cuni]
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _

theorem nb071_support_mem_0047 (x : Var) : x ∈ (((synCuni (Class.cv x))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0048 (x : Var) :
    x ∈
      (({(nb071AlphaDummy043 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
            (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
              (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wrex]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb071AlphaDummy044 x) from (by
          unfold nb071AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0047 x) 1))))
  · rw [fv_syn_cuni]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb071_support_mem_0049 (x : Var) :
    x ∈
      (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq (Class.cab (nb071AlphaDummy043 x)
              (synWa (Wff.classMem (Class.cv (nb071AlphaDummy043 x)) (synCncs))
                (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
                    (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))))
            (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb071AlphaDummy046 x) from (by
          unfold nb071AlphaDummy046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0048 x) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb071AlphaDummy043 x) from (by
            unfold nb071AlphaDummy043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0047 x) 0))))
    · rw [fv_syn_wa]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact
          (show x ≠ (nb071AlphaDummy044 x) from (by
              unfold nb071AlphaDummy044;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0047 x) 1))))
      · rw [fv_syn_cuni]
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _

theorem nb071_support_mem_0050 :
    (nb071AlphaDummy000) ∈ (((Class.cv (nb071AlphaDummy000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0051 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0052 :
    (nb071AlphaDummy065) ∈
      (((synCnin (Class.cv (nb071AlphaDummy065)) (Class.cv (nb071AlphaDummy042)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy065))
            (Class.cv (nb071AlphaDummy042)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0053 (x : Var) :
    (nb071AlphaDummy066 x) ∈
      (((synCnin (Class.cv (nb071AlphaDummy066 x))
            (Class.cv (nb071AlphaDummy044 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy066 x))
            (Class.cv (nb071AlphaDummy044 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
