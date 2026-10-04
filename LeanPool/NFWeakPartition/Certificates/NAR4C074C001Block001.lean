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

/-! Certificates from `NAR4C074C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_000`. -/
@[expose]
noncomputable def nb074AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_001`. -/
@[expose]
noncomputable def nb074AlphaDummy001 : Var :=
  (freshVar (({(nb074AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCdm (Class.cv (nb074AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_002`. -/
@[expose]
noncomputable def nb074AlphaDummy002 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCdm (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_003`. -/
@[expose]
noncomputable def nb074AlphaDummy003 : Var :=
  (freshVar
    (({(nb074AlphaDummy000)} : Finset Var) ∪ ({(nb074AlphaDummy001)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb074AlphaDummy000)) (synCvv))
          (Wff.classEq (Class.cv (nb074AlphaDummy001))
            (synCdm (Class.cv (nb074AlphaDummy000)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_004`. -/
@[expose]
noncomputable def nb074AlphaDummy004 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb074AlphaDummy002 x)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv x) (synCvv))
          (Wff.classEq (Class.cv (nb074AlphaDummy002 x)) (synCdm (Class.cv x))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_005`. -/
@[expose]
noncomputable def nb074AlphaDummy005 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_006`. -/
@[expose]
noncomputable def nb074AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_007`. -/
@[expose]
noncomputable def nb074AlphaDummy007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_008`. -/
@[expose]
noncomputable def nb074AlphaDummy008 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_009`. -/
@[expose]
noncomputable def nb074AlphaDummy009 : Var :=
  (freshVar (((synCcompl (Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCphi (Class.cv (nb074AlphaDummy006)))))))).fv ∪ ((synCcompl
          (Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_010`. -/
@[expose]
noncomputable def nb074AlphaDummy010 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCphi (Class.cv (nb074AlphaDummy008 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_011`. -/
@[expose]
noncomputable def nb074AlphaDummy011 : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy005)
          (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
            (Wff.classEq (Class.cv (nb074AlphaDummy005))
              (synCphi (Class.cv (nb074AlphaDummy006))))))).fv ∪
      ((Class.cab (nb074AlphaDummy005)
          (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
            (Wff.classEq (Class.cv (nb074AlphaDummy005))
              (synCphi (Class.cv (nb074AlphaDummy006))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_012`. -/
@[expose]
noncomputable def nb074AlphaDummy012 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy007 x)
          (synWrex (nb074AlphaDummy008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
              (synCphi (Class.cv (nb074AlphaDummy008 x))))))).fv ∪
      ((Class.cab (nb074AlphaDummy007 x) (synWrex (nb074AlphaDummy008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
              (synCphi (Class.cv (nb074AlphaDummy008 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_013`. -/
@[expose]
noncomputable def nb074AlphaDummy013 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_014`. -/
@[expose]
noncomputable def nb074AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy006))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_015`. -/
@[expose]
noncomputable def nb074AlphaDummy015 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy008 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_016`. -/
@[expose]
noncomputable def nb074AlphaDummy016 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy008 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_017`. -/
@[expose]
noncomputable def nb074AlphaDummy017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074AlphaDummy013)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb074AlphaDummy013)) (synC1c))).fv ∪
      ((Class.cv (nb074AlphaDummy013))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_018`. -/
@[expose]
noncomputable def nb074AlphaDummy018 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074AlphaDummy015 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb074AlphaDummy015 x)) (synC1c))).fv ∪
      ((Class.cv (nb074AlphaDummy015 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_019`. -/
@[expose]
noncomputable def nb074AlphaDummy019 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_020`. -/
@[expose]
noncomputable def nb074AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_021`. -/
@[expose]
noncomputable def nb074AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_022`. -/
@[expose]
noncomputable def nb074AlphaDummy022 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_023`. -/
@[expose]
noncomputable def nb074AlphaDummy023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_024`. -/
@[expose]
noncomputable def nb074AlphaDummy024 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_025`. -/
@[expose]
noncomputable def nb074AlphaDummy025 : Var :=
  (freshVar (((synCnin (Class.cv (nb074AlphaDummy020))
          (Class.cv (nb074AlphaDummy021)))).fv ∪
      ((synCnin (Class.cv (nb074AlphaDummy020)) (Class.cv (nb074AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_026`. -/
@[expose]
noncomputable def nb074AlphaDummy026 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb074AlphaDummy023 x))
          (Class.cv (nb074AlphaDummy024 x)))).fv ∪
      ((synCnin (Class.cv (nb074AlphaDummy023 x)) (Class.cv (nb074AlphaDummy024 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_027`. -/
@[expose]
noncomputable def nb074AlphaDummy027 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_028`. -/
@[expose]
noncomputable def nb074AlphaDummy028 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy023 x))).fv ∪
      ((Class.cv (nb074AlphaDummy024 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_029`. -/
@[expose]
noncomputable def nb074AlphaDummy029 : Var :=
  (freshVar (((synCcompl (Class.cv (nb074AlphaDummy020)))).fv ∪
      ((synCcompl (Class.cv (nb074AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_030`. -/
@[expose]
noncomputable def nb074AlphaDummy030 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb074AlphaDummy023 x)))).fv ∪
      ((synCcompl (Class.cv (nb074AlphaDummy024 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_031`. -/
@[expose]
noncomputable def nb074AlphaDummy031 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_032`. -/
@[expose]
noncomputable def nb074AlphaDummy032 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy023 x))).fv ∪
      ((Class.cv (nb074AlphaDummy023 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_033`. -/
@[expose]
noncomputable def nb074AlphaDummy033 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy021))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_034`. -/
@[expose]
noncomputable def nb074AlphaDummy034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy024 x))).fv ∪
      ((Class.cv (nb074AlphaDummy024 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_035`. -/
@[expose]
noncomputable def nb074AlphaDummy035 : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy005)
          (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
            (Wff.classEq (Class.cv (nb074AlphaDummy005))
              (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy005)
          (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
            (Wff.classEq (Class.cv (nb074AlphaDummy005))
              (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_036`. -/
@[expose]
noncomputable def nb074AlphaDummy036 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy007 x)
          (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
              (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy007 x)
          (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
              (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_037`. -/
@[expose]
noncomputable def nb074AlphaDummy037 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb074AlphaDummy006))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_038`. -/
@[expose]
noncomputable def nb074AlphaDummy038 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb074AlphaDummy008 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_039`. -/
@[expose]
noncomputable def nb074AlphaDummy039 : Var :=
  (freshVar (((synCphi (Class.cv (nb074AlphaDummy006)))).fv ∪
      ((synCphi (Class.cv (nb074AlphaDummy006)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_040`. -/
@[expose]
noncomputable def nb074AlphaDummy040 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb074AlphaDummy008 x)))).fv ∪
      ((synCphi (Class.cv (nb074AlphaDummy008 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_041`. -/
@[expose]
noncomputable def nb074AlphaDummy041 : Var :=
  (freshVar (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_042`. -/
@[expose]
noncomputable def nb074AlphaDummy042 : Var :=
  (freshVar (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_043`. -/
@[expose]
noncomputable def nb074AlphaDummy043 (x : Var) : Var :=
  (freshVar (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_044`. -/
@[expose]
noncomputable def nb074AlphaDummy044 (x : Var) : Var :=
  (freshVar (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_045`. -/
@[expose]
noncomputable def nb074AlphaDummy045 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_046`. -/
@[expose]
noncomputable def nb074AlphaDummy046 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_047`. -/
@[expose]
noncomputable def nb074AlphaDummy047 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy044 x))).fv ∪
      ((Class.cv (nb074AlphaDummy043 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_048`. -/
@[expose]
noncomputable def nb074AlphaDummy048 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy044 x))).fv ∪
      ((Class.cv (nb074AlphaDummy043 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_049`. -/
@[expose]
noncomputable def nb074AlphaDummy049 : Var :=
  (freshVar (((synCcompl (Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCphi (Class.cv (nb074AlphaDummy046)))))))).fv ∪ ((synCcompl
          (Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_050`. -/
@[expose]
noncomputable def nb074AlphaDummy050 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCphi (Class.cv (nb074AlphaDummy048 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_051`. -/
@[expose]
noncomputable def nb074AlphaDummy051 : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy045)
          (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
            (Wff.classEq (Class.cv (nb074AlphaDummy045))
              (synCphi (Class.cv (nb074AlphaDummy046))))))).fv ∪
      ((Class.cab (nb074AlphaDummy045)
          (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
            (Wff.classEq (Class.cv (nb074AlphaDummy045))
              (synCphi (Class.cv (nb074AlphaDummy046))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_052`. -/
@[expose]
noncomputable def nb074AlphaDummy052 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy047 x)
          (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
              (synCphi (Class.cv (nb074AlphaDummy048 x))))))).fv ∪
      ((Class.cab (nb074AlphaDummy047 x)
          (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
              (synCphi (Class.cv (nb074AlphaDummy048 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_053`. -/
@[expose]
noncomputable def nb074AlphaDummy053 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy046))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_054`. -/
@[expose]
noncomputable def nb074AlphaDummy054 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy046))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_055`. -/
@[expose]
noncomputable def nb074AlphaDummy055 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy048 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_056`. -/
@[expose]
noncomputable def nb074AlphaDummy056 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy048 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_057`. -/
@[expose]
noncomputable def nb074AlphaDummy057 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074AlphaDummy053)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb074AlphaDummy053)) (synC1c))).fv ∪
      ((Class.cv (nb074AlphaDummy053))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_058`. -/
@[expose]
noncomputable def nb074AlphaDummy058 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074AlphaDummy055 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb074AlphaDummy055 x)) (synC1c))).fv ∪
      ((Class.cv (nb074AlphaDummy055 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_059`. -/
@[expose]
noncomputable def nb074AlphaDummy059 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_060`. -/
@[expose]
noncomputable def nb074AlphaDummy060 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_061`. -/
@[expose]
noncomputable def nb074AlphaDummy061 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_062`. -/
@[expose]
noncomputable def nb074AlphaDummy062 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_063`. -/
@[expose]
noncomputable def nb074AlphaDummy063 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_064`. -/
@[expose]
noncomputable def nb074AlphaDummy064 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_065`. -/
@[expose]
noncomputable def nb074AlphaDummy065 : Var :=
  (freshVar (((synCnin (Class.cv (nb074AlphaDummy060))
          (Class.cv (nb074AlphaDummy061)))).fv ∪
      ((synCnin (Class.cv (nb074AlphaDummy060)) (Class.cv (nb074AlphaDummy061)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_066`. -/
@[expose]
noncomputable def nb074AlphaDummy066 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb074AlphaDummy063 x))
          (Class.cv (nb074AlphaDummy064 x)))).fv ∪
      ((synCnin (Class.cv (nb074AlphaDummy063 x)) (Class.cv (nb074AlphaDummy064 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_067`. -/
@[expose]
noncomputable def nb074AlphaDummy067 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_068`. -/
@[expose]
noncomputable def nb074AlphaDummy068 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy063 x))).fv ∪
      ((Class.cv (nb074AlphaDummy064 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_069`. -/
@[expose]
noncomputable def nb074AlphaDummy069 : Var :=
  (freshVar (((synCcompl (Class.cv (nb074AlphaDummy060)))).fv ∪
      ((synCcompl (Class.cv (nb074AlphaDummy061)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_070`. -/
@[expose]
noncomputable def nb074AlphaDummy070 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb074AlphaDummy063 x)))).fv ∪
      ((synCcompl (Class.cv (nb074AlphaDummy064 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_071`. -/
@[expose]
noncomputable def nb074AlphaDummy071 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy060))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_072`. -/
@[expose]
noncomputable def nb074AlphaDummy072 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy063 x))).fv ∪
      ((Class.cv (nb074AlphaDummy063 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_073`. -/
@[expose]
noncomputable def nb074AlphaDummy073 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy061))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_074`. -/
@[expose]
noncomputable def nb074AlphaDummy074 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy064 x))).fv ∪
      ((Class.cv (nb074AlphaDummy064 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_075`. -/
@[expose]
noncomputable def nb074AlphaDummy075 : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy045)
          (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
            (Wff.classEq (Class.cv (nb074AlphaDummy045))
              (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy045)
          (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
            (Wff.classEq (Class.cv (nb074AlphaDummy045))
              (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_076`. -/
@[expose]
noncomputable def nb074AlphaDummy076 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy047 x)
          (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
              (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy047 x)
          (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
              (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_077`. -/
@[expose]
noncomputable def nb074AlphaDummy077 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb074AlphaDummy046))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_078`. -/
@[expose]
noncomputable def nb074AlphaDummy078 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb074AlphaDummy048 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_079`. -/
@[expose]
noncomputable def nb074AlphaDummy079 : Var :=
  (freshVar (((synCphi (Class.cv (nb074AlphaDummy046)))).fv ∪
      ((synCphi (Class.cv (nb074AlphaDummy046)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_080`. -/
@[expose]
noncomputable def nb074AlphaDummy080 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb074AlphaDummy048 x)))).fv ∪
      ((synCphi (Class.cv (nb074AlphaDummy048 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_081`. -/
@[expose]
noncomputable def nb074AlphaDummy081 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_082`. -/
@[expose]
noncomputable def nb074AlphaDummy082 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_083`. -/
@[expose]
noncomputable def nb074AlphaDummy083 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_084`. -/
@[expose]
noncomputable def nb074AlphaDummy084 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_085`. -/
@[expose]
noncomputable def nb074AlphaDummy085 : Var :=
  (freshVar
    (({(nb074AlphaDummy081)} : Finset Var) ∪ ({(nb074AlphaDummy082)} : Finset Var) ∪
      ((synWbr (Class.cv (nb074AlphaDummy082)) (Class.cv (nb074AlphaDummy000))
          (Class.cv (nb074AlphaDummy081)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_086`. -/
@[expose]
noncomputable def nb074AlphaDummy086 (x : Var) : Var :=
  (freshVar (({(nb074AlphaDummy083 x)} : Finset Var) ∪
        ({(nb074AlphaDummy084 x)} : Finset Var) ∪
      ((synWbr (Class.cv (nb074AlphaDummy084 x)) (Class.cv x)
          (Class.cv (nb074AlphaDummy083 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_087`. -/
@[expose]
noncomputable def nb074AlphaDummy087 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_088`. -/
@[expose]
noncomputable def nb074AlphaDummy088 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_089`. -/
@[expose]
noncomputable def nb074AlphaDummy089 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy083 x))).fv ∪
      ((Class.cv (nb074AlphaDummy084 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_090`. -/
@[expose]
noncomputable def nb074AlphaDummy090 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy083 x))).fv ∪
      ((Class.cv (nb074AlphaDummy084 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_091`. -/
@[expose]
noncomputable def nb074AlphaDummy091 : Var :=
  (freshVar (((synCcompl (Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCphi (Class.cv (nb074AlphaDummy088)))))))).fv ∪ ((synCcompl
          (Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_092`. -/
@[expose]
noncomputable def nb074AlphaDummy092 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCphi (Class.cv (nb074AlphaDummy090 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_093`. -/
@[expose]
noncomputable def nb074AlphaDummy093 : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy087)
          (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
            (Wff.classEq (Class.cv (nb074AlphaDummy087))
              (synCphi (Class.cv (nb074AlphaDummy088))))))).fv ∪
      ((Class.cab (nb074AlphaDummy087)
          (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
            (Wff.classEq (Class.cv (nb074AlphaDummy087))
              (synCphi (Class.cv (nb074AlphaDummy088))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_094`. -/
@[expose]
noncomputable def nb074AlphaDummy094 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy089 x)
          (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
              (synCphi (Class.cv (nb074AlphaDummy090 x))))))).fv ∪
      ((Class.cab (nb074AlphaDummy089 x)
          (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
              (synCphi (Class.cv (nb074AlphaDummy090 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_095`. -/
@[expose]
noncomputable def nb074AlphaDummy095 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy088))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_096`. -/
@[expose]
noncomputable def nb074AlphaDummy096 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy088))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_097`. -/
@[expose]
noncomputable def nb074AlphaDummy097 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy090 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_098`. -/
@[expose]
noncomputable def nb074AlphaDummy098 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy090 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_099`. -/
@[expose]
noncomputable def nb074AlphaDummy099 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074AlphaDummy095)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb074AlphaDummy095)) (synC1c))).fv ∪
      ((Class.cv (nb074AlphaDummy095))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_100`. -/
@[expose]
noncomputable def nb074AlphaDummy100 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074AlphaDummy097 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb074AlphaDummy097 x)) (synC1c))).fv ∪
      ((Class.cv (nb074AlphaDummy097 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_101`. -/
@[expose]
noncomputable def nb074AlphaDummy101 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_102`. -/
@[expose]
noncomputable def nb074AlphaDummy102 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_103`. -/
@[expose]
noncomputable def nb074AlphaDummy103 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_104`. -/
@[expose]
noncomputable def nb074AlphaDummy104 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_105`. -/
@[expose]
noncomputable def nb074AlphaDummy105 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_106`. -/
@[expose]
noncomputable def nb074AlphaDummy106 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_107`. -/
@[expose]
noncomputable def nb074AlphaDummy107 : Var :=
  (freshVar (((synCnin (Class.cv (nb074AlphaDummy102))
          (Class.cv (nb074AlphaDummy103)))).fv ∪
      ((synCnin (Class.cv (nb074AlphaDummy102)) (Class.cv (nb074AlphaDummy103)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_108`. -/
@[expose]
noncomputable def nb074AlphaDummy108 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb074AlphaDummy105 x))
          (Class.cv (nb074AlphaDummy106 x)))).fv ∪
      ((synCnin (Class.cv (nb074AlphaDummy105 x)) (Class.cv (nb074AlphaDummy106 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_109`. -/
@[expose]
noncomputable def nb074AlphaDummy109 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_110`. -/
@[expose]
noncomputable def nb074AlphaDummy110 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy105 x))).fv ∪
      ((Class.cv (nb074AlphaDummy106 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_111`. -/
@[expose]
noncomputable def nb074AlphaDummy111 : Var :=
  (freshVar (((synCcompl (Class.cv (nb074AlphaDummy102)))).fv ∪
      ((synCcompl (Class.cv (nb074AlphaDummy103)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_112`. -/
@[expose]
noncomputable def nb074AlphaDummy112 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb074AlphaDummy105 x)))).fv ∪
      ((synCcompl (Class.cv (nb074AlphaDummy106 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_113`. -/
@[expose]
noncomputable def nb074AlphaDummy113 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy102))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_114`. -/
@[expose]
noncomputable def nb074AlphaDummy114 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy105 x))).fv ∪
      ((Class.cv (nb074AlphaDummy105 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_115`. -/
@[expose]
noncomputable def nb074AlphaDummy115 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy103))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_116`. -/
@[expose]
noncomputable def nb074AlphaDummy116 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy106 x))).fv ∪
      ((Class.cv (nb074AlphaDummy106 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_117`. -/
@[expose]
noncomputable def nb074AlphaDummy117 : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy087)
          (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
            (Wff.classEq (Class.cv (nb074AlphaDummy087))
              (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy087)
          (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
            (Wff.classEq (Class.cv (nb074AlphaDummy087))
              (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_118`. -/
@[expose]
noncomputable def nb074AlphaDummy118 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy089 x)
          (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
              (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy089 x)
          (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
              (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_119`. -/
@[expose]
noncomputable def nb074AlphaDummy119 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb074AlphaDummy088))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_120`. -/
@[expose]
noncomputable def nb074AlphaDummy120 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb074AlphaDummy090 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_121`. -/
@[expose]
noncomputable def nb074AlphaDummy121 : Var :=
  (freshVar (((synCphi (Class.cv (nb074AlphaDummy088)))).fv ∪
      ((synCphi (Class.cv (nb074AlphaDummy088)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_122`. -/
@[expose]
noncomputable def nb074AlphaDummy122 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb074AlphaDummy090 x)))).fv ∪
      ((synCphi (Class.cv (nb074AlphaDummy090 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_123`. -/
@[expose]
noncomputable def nb074AlphaDummy123 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_124`. -/
@[expose]
noncomputable def nb074AlphaDummy124 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_125`. -/
@[expose]
noncomputable def nb074AlphaDummy125 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy084 x))).fv ∪
      ((Class.cv (nb074AlphaDummy083 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_126`. -/
@[expose]
noncomputable def nb074AlphaDummy126 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy084 x))).fv ∪
      ((Class.cv (nb074AlphaDummy083 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_127`. -/
@[expose]
noncomputable def nb074AlphaDummy127 : Var :=
  (freshVar (((synCcompl (Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCphi (Class.cv (nb074AlphaDummy124)))))))).fv ∪ ((synCcompl
          (Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_128`. -/
@[expose]
noncomputable def nb074AlphaDummy128 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCphi (Class.cv (nb074AlphaDummy126 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_129`. -/
@[expose]
noncomputable def nb074AlphaDummy129 : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy123)
          (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
            (Wff.classEq (Class.cv (nb074AlphaDummy123))
              (synCphi (Class.cv (nb074AlphaDummy124))))))).fv ∪
      ((Class.cab (nb074AlphaDummy123)
          (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
            (Wff.classEq (Class.cv (nb074AlphaDummy123))
              (synCphi (Class.cv (nb074AlphaDummy124))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_130`. -/
@[expose]
noncomputable def nb074AlphaDummy130 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy125 x)
          (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
              (synCphi (Class.cv (nb074AlphaDummy126 x))))))).fv ∪
      ((Class.cab (nb074AlphaDummy125 x)
          (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
              (synCphi (Class.cv (nb074AlphaDummy126 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_131`. -/
@[expose]
noncomputable def nb074AlphaDummy131 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy124))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_132`. -/
@[expose]
noncomputable def nb074AlphaDummy132 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy124))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_133`. -/
@[expose]
noncomputable def nb074AlphaDummy133 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy126 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_134`. -/
@[expose]
noncomputable def nb074AlphaDummy134 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy126 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_135`. -/
@[expose]
noncomputable def nb074AlphaDummy135 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074AlphaDummy131)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb074AlphaDummy131)) (synC1c))).fv ∪
      ((Class.cv (nb074AlphaDummy131))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_136`. -/
@[expose]
noncomputable def nb074AlphaDummy136 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb074AlphaDummy133 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb074AlphaDummy133 x)) (synC1c))).fv ∪
      ((Class.cv (nb074AlphaDummy133 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_137`. -/
@[expose]
noncomputable def nb074AlphaDummy137 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_138`. -/
@[expose]
noncomputable def nb074AlphaDummy138 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_139`. -/
@[expose]
noncomputable def nb074AlphaDummy139 : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_140`. -/
@[expose]
noncomputable def nb074AlphaDummy140 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_141`. -/
@[expose]
noncomputable def nb074AlphaDummy141 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_142`. -/
@[expose]
noncomputable def nb074AlphaDummy142 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_143`. -/
@[expose]
noncomputable def nb074AlphaDummy143 : Var :=
  (freshVar (((synCnin (Class.cv (nb074AlphaDummy138))
          (Class.cv (nb074AlphaDummy139)))).fv ∪
      ((synCnin (Class.cv (nb074AlphaDummy138)) (Class.cv (nb074AlphaDummy139)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_144`. -/
@[expose]
noncomputable def nb074AlphaDummy144 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb074AlphaDummy141 x))
          (Class.cv (nb074AlphaDummy142 x)))).fv ∪
      ((synCnin (Class.cv (nb074AlphaDummy141 x)) (Class.cv (nb074AlphaDummy142 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_145`. -/
@[expose]
noncomputable def nb074AlphaDummy145 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_146`. -/
@[expose]
noncomputable def nb074AlphaDummy146 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy141 x))).fv ∪
      ((Class.cv (nb074AlphaDummy142 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_147`. -/
@[expose]
noncomputable def nb074AlphaDummy147 : Var :=
  (freshVar (((synCcompl (Class.cv (nb074AlphaDummy138)))).fv ∪
      ((synCcompl (Class.cv (nb074AlphaDummy139)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_148`. -/
@[expose]
noncomputable def nb074AlphaDummy148 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb074AlphaDummy141 x)))).fv ∪
      ((synCcompl (Class.cv (nb074AlphaDummy142 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_149`. -/
@[expose]
noncomputable def nb074AlphaDummy149 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy138))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_150`. -/
@[expose]
noncomputable def nb074AlphaDummy150 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy141 x))).fv ∪
      ((Class.cv (nb074AlphaDummy141 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_151`. -/
@[expose]
noncomputable def nb074AlphaDummy151 : Var :=
  (freshVar
    (((Class.cv (nb074AlphaDummy139))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_152`. -/
@[expose]
noncomputable def nb074AlphaDummy152 (x : Var) : Var :=
  (freshVar (((Class.cv (nb074AlphaDummy142 x))).fv ∪
      ((Class.cv (nb074AlphaDummy142 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_153`. -/
@[expose]
noncomputable def nb074AlphaDummy153 : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy123)
          (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
            (Wff.classEq (Class.cv (nb074AlphaDummy123))
              (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy123)
          (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
            (Wff.classEq (Class.cv (nb074AlphaDummy123))
              (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_154`. -/
@[expose]
noncomputable def nb074AlphaDummy154 (x : Var) : Var :=
  (freshVar (((Class.cab (nb074AlphaDummy125 x)
          (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
              (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy125 x)
          (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
            (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
              (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_155`. -/
@[expose]
noncomputable def nb074AlphaDummy155 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb074AlphaDummy124))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_156`. -/
@[expose]
noncomputable def nb074AlphaDummy156 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb074AlphaDummy126 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_157`. -/
@[expose]
noncomputable def nb074AlphaDummy157 : Var :=
  (freshVar (((synCphi (Class.cv (nb074AlphaDummy124)))).fv ∪
      ((synCphi (Class.cv (nb074AlphaDummy124)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb074_alpha_dummy_158`. -/
@[expose]
noncomputable def nb074AlphaDummy158 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb074AlphaDummy126 x)))).fv ∪
      ((synCphi (Class.cv (nb074AlphaDummy126 x)))).fv) 0)

theorem nb074_fresh_000 :
    (nb074AlphaDummy011) ∉
      (((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCphi (Class.cv (nb074AlphaDummy006))))))).fv ∪
        ((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCphi (Class.cv (nb074AlphaDummy006))))))).fv) :=
  by
  simpa only [nb074AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCphi (Class.cv (nb074AlphaDummy006))))))).fv ∪
        ((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCphi (Class.cv (nb074AlphaDummy006))))))).fv)
      0

theorem nb074_fresh_001 :
    (nb074AlphaDummy035) ∉
      (((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb074AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb074_fresh_002 (x : Var) :
    (nb074AlphaDummy036 x) ∉
      (((Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb074AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb074_fresh_003 (x : Var) :
    (nb074AlphaDummy012 x) ∉
      (((Class.cab (nb074AlphaDummy007 x) (synWrex (nb074AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCphi (Class.cv (nb074AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy007 x) (synWrex (nb074AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCphi (Class.cv (nb074AlphaDummy008 x))))))).fv) :=
  by
  simpa only [nb074AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy007 x) (synWrex (nb074AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCphi (Class.cv (nb074AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy007 x) (synWrex (nb074AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCphi (Class.cv (nb074AlphaDummy008 x))))))).fv)
      0

theorem nb074_fresh_004 :
    (nb074AlphaDummy075) ∉
      (((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb074AlphaDummy075] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb074_fresh_005 :
    (nb074AlphaDummy051) ∉
      (((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCphi (Class.cv (nb074AlphaDummy046))))))).fv ∪
        ((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCphi (Class.cv (nb074AlphaDummy046))))))).fv) :=
  by
  simpa only [nb074AlphaDummy051] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCphi (Class.cv (nb074AlphaDummy046))))))).fv ∪
        ((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCphi (Class.cv (nb074AlphaDummy046))))))).fv)
      0

theorem nb074_fresh_006 (x : Var) :
    (nb074AlphaDummy076 x) ∉
      (((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb074AlphaDummy076] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb074_fresh_007 (x : Var) :
    (nb074AlphaDummy052 x) ∉
      (((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCphi (Class.cv (nb074AlphaDummy048 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCphi (Class.cv (nb074AlphaDummy048 x))))))).fv) :=
  by
  simpa only [nb074AlphaDummy052] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCphi (Class.cv (nb074AlphaDummy048 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCphi (Class.cv (nb074AlphaDummy048 x))))))).fv)
      0

theorem nb074_fresh_008 :
    (nb074AlphaDummy093) ∉
      (((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCphi (Class.cv (nb074AlphaDummy088))))))).fv ∪
        ((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCphi (Class.cv (nb074AlphaDummy088))))))).fv) :=
  by
  simpa only [nb074AlphaDummy093] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCphi (Class.cv (nb074AlphaDummy088))))))).fv ∪
        ((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCphi (Class.cv (nb074AlphaDummy088))))))).fv)
      0

theorem nb074_fresh_009 :
    (nb074AlphaDummy117) ∉
      (((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb074AlphaDummy117] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb074_fresh_010 (x : Var) :
    (nb074AlphaDummy094 x) ∉
      (((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCphi (Class.cv (nb074AlphaDummy090 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCphi (Class.cv (nb074AlphaDummy090 x))))))).fv) :=
  by
  simpa only [nb074AlphaDummy094] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCphi (Class.cv (nb074AlphaDummy090 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCphi (Class.cv (nb074AlphaDummy090 x))))))).fv)
      0

theorem nb074_fresh_011 (x : Var) :
    (nb074AlphaDummy118 x) ∉
      (((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb074AlphaDummy118] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb074_fresh_012 :
    (nb074AlphaDummy153) ∉
      (((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb074AlphaDummy153] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb074_fresh_013 :
    (nb074AlphaDummy129) ∉
      (((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCphi (Class.cv (nb074AlphaDummy124))))))).fv ∪
        ((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCphi (Class.cv (nb074AlphaDummy124))))))).fv) :=
  by
  simpa only [nb074AlphaDummy129] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCphi (Class.cv (nb074AlphaDummy124))))))).fv ∪
        ((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCphi (Class.cv (nb074AlphaDummy124))))))).fv)
      0

theorem nb074_fresh_014 (x : Var) :
    (nb074AlphaDummy154 x) ∉
      (((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb074AlphaDummy154] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb074_fresh_015 (x : Var) :
    (nb074AlphaDummy130 x) ∉
      (((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCphi (Class.cv (nb074AlphaDummy126 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCphi (Class.cv (nb074AlphaDummy126 x))))))).fv) :=
  by
  simpa only [nb074AlphaDummy130] using
    freshVar_not_mem
      (((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCphi (Class.cv (nb074AlphaDummy126 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCphi (Class.cv (nb074AlphaDummy126 x))))))).fv)
      0

theorem nb074_fresh_016 :
    (nb074AlphaDummy081) ∉ (((Class.cv (nb074AlphaDummy000))).fv) := by
  simpa only [nb074AlphaDummy081] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy000))).fv) 0

theorem nb074_fresh_017 :
    (nb074AlphaDummy082) ∉ (((Class.cv (nb074AlphaDummy000))).fv) := by
  simpa only [nb074AlphaDummy082] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy000))).fv) 1

theorem nb074_distinct_018 : (nb074AlphaDummy081) ≠ (nb074AlphaDummy082) := by
  simpa only [nb074AlphaDummy081, nb074AlphaDummy082] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy000))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_019 :
    (nb074AlphaDummy005) ∉
      (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv) :=
  by
  simpa only [nb074AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv)
      0

theorem nb074_fresh_020 :
    (nb074AlphaDummy006) ∉
      (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv) :=
  by
  simpa only [nb074AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv)
      1

theorem nb074_distinct_021 : (nb074AlphaDummy005) ≠ (nb074AlphaDummy006) := by
  simpa only [nb074AlphaDummy005, nb074AlphaDummy006] using
    (freshVar_injective
      (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_022 :
    (nb074AlphaDummy013) ∉ (((Class.cv (nb074AlphaDummy006))).fv) := by
  simpa only [nb074AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy006))).fv) 0

theorem nb074_fresh_023 :
    (nb074AlphaDummy014) ∉ (((Class.cv (nb074AlphaDummy006))).fv) := by
  simpa only [nb074AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy006))).fv) 1

theorem nb074_distinct_024 : (nb074AlphaDummy013) ≠ (nb074AlphaDummy014) := by
  simpa only [nb074AlphaDummy013, nb074AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy006))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_025 (x : Var) :
    (nb074AlphaDummy015 x) ∉ (((Class.cv (nb074AlphaDummy008 x))).fv) := by
  simpa only [nb074AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy008 x))).fv) 0

theorem nb074_fresh_026 (x : Var) :
    (nb074AlphaDummy016 x) ∉ (((Class.cv (nb074AlphaDummy008 x))).fv) := by
  simpa only [nb074AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy008 x))).fv) 1

theorem nb074_distinct_027 (x : Var) :
    (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy016 x) := by
  simpa only [nb074AlphaDummy015, nb074AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy008 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_028 :
    (nb074AlphaDummy019) ∉
      (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) 0

theorem nb074_fresh_029 :
    (nb074AlphaDummy020) ∉
      (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) 1

theorem nb074_fresh_030 :
    (nb074AlphaDummy021) ∉
      (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) 2

theorem nb074_distinct_031 : (nb074AlphaDummy019) ≠ (nb074AlphaDummy020) := by
  simpa only [nb074AlphaDummy019, nb074AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_032 : (nb074AlphaDummy019) ≠ (nb074AlphaDummy021) := by
  simpa only [nb074AlphaDummy019, nb074AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_033 : (nb074AlphaDummy020) ≠ (nb074AlphaDummy021) := by
  simpa only [nb074AlphaDummy020, nb074AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_034 (x : Var) :
    (nb074AlphaDummy022 x) ∉
      (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 0

theorem nb074_fresh_035 (x : Var) :
    (nb074AlphaDummy023 x) ∉
      (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 1

theorem nb074_fresh_036 (x : Var) :
    (nb074AlphaDummy024 x) ∉
      (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) 2

theorem nb074_distinct_037 (x : Var) :
    (nb074AlphaDummy022 x) ≠ (nb074AlphaDummy023 x) := by
  simpa only [nb074AlphaDummy022, nb074AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_038 (x : Var) :
    (nb074AlphaDummy022 x) ≠ (nb074AlphaDummy024 x) := by
  simpa only [nb074AlphaDummy022, nb074AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_039 (x : Var) :
    (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy024 x) := by
  simpa only [nb074AlphaDummy023, nb074AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_040 :
    (nb074AlphaDummy031) ∉
      (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy020))).fv) :=
  by
  simpa only [nb074AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy020))).fv)
      0

theorem nb074_fresh_041 :
    (nb074AlphaDummy027) ∉
      (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv) :=
  by
  simpa only [nb074AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv)
      0

theorem nb074_fresh_042 :
    (nb074AlphaDummy033) ∉
      (((Class.cv (nb074AlphaDummy021))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv) :=
  by
  simpa only [nb074AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy021))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv)
      0

theorem nb074_fresh_043 (x : Var) :
    (nb074AlphaDummy032 x) ∉
      (((Class.cv (nb074AlphaDummy023 x))).fv ∪ ((Class.cv (nb074AlphaDummy023 x))).fv) :=
  by
  simpa only [nb074AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy023 x))).fv ∪ ((Class.cv (nb074AlphaDummy023 x))).fv)
      0

theorem nb074_fresh_044 (x : Var) :
    (nb074AlphaDummy028 x) ∉
      (((Class.cv (nb074AlphaDummy023 x))).fv ∪ ((Class.cv (nb074AlphaDummy024 x))).fv) :=
  by
  simpa only [nb074AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy023 x))).fv ∪ ((Class.cv (nb074AlphaDummy024 x))).fv)
      0

theorem nb074_fresh_045 (x : Var) :
    (nb074AlphaDummy034 x) ∉
      (((Class.cv (nb074AlphaDummy024 x))).fv ∪ ((Class.cv (nb074AlphaDummy024 x))).fv) :=
  by
  simpa only [nb074AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy024 x))).fv ∪ ((Class.cv (nb074AlphaDummy024 x))).fv)
      0

theorem nb074_fresh_046 :
    (nb074AlphaDummy045) ∉
      (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv) :=
  by
  simpa only [nb074AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv)
      0

theorem nb074_fresh_047 :
    (nb074AlphaDummy046) ∉
      (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv) :=
  by
  simpa only [nb074AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv)
      1

theorem nb074_distinct_048 : (nb074AlphaDummy045) ≠ (nb074AlphaDummy046) := by
  simpa only [nb074AlphaDummy045, nb074AlphaDummy046] using
    (freshVar_injective
      (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_049 (x : Var) :
    (nb074AlphaDummy047 x) ∉
      (((Class.cv (nb074AlphaDummy044 x))).fv ∪ ((Class.cv (nb074AlphaDummy043 x))).fv) :=
  by
  simpa only [nb074AlphaDummy047] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy044 x))).fv ∪ ((Class.cv (nb074AlphaDummy043 x))).fv)
      0

theorem nb074_fresh_050 (x : Var) :
    (nb074AlphaDummy048 x) ∉
      (((Class.cv (nb074AlphaDummy044 x))).fv ∪ ((Class.cv (nb074AlphaDummy043 x))).fv) :=
  by
  simpa only [nb074AlphaDummy048] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy044 x))).fv ∪ ((Class.cv (nb074AlphaDummy043 x))).fv)
      1

theorem nb074_distinct_051 (x : Var) :
    (nb074AlphaDummy047 x) ≠ (nb074AlphaDummy048 x) := by
  simpa only [nb074AlphaDummy047, nb074AlphaDummy048] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy044 x))).fv ∪
        ((Class.cv (nb074AlphaDummy043 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_052 :
    (nb074AlphaDummy053) ∉ (((Class.cv (nb074AlphaDummy046))).fv) := by
  simpa only [nb074AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy046))).fv) 0

theorem nb074_fresh_053 :
    (nb074AlphaDummy054) ∉ (((Class.cv (nb074AlphaDummy046))).fv) := by
  simpa only [nb074AlphaDummy054] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy046))).fv) 1

theorem nb074_distinct_054 : (nb074AlphaDummy053) ≠ (nb074AlphaDummy054) := by
  simpa only [nb074AlphaDummy053, nb074AlphaDummy054] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy046))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_055 (x : Var) :
    (nb074AlphaDummy055 x) ∉ (((Class.cv (nb074AlphaDummy048 x))).fv) := by
  simpa only [nb074AlphaDummy055] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy048 x))).fv) 0

theorem nb074_fresh_056 (x : Var) :
    (nb074AlphaDummy056 x) ∉ (((Class.cv (nb074AlphaDummy048 x))).fv) := by
  simpa only [nb074AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy048 x))).fv) 1

theorem nb074_distinct_057 (x : Var) :
    (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy056 x) := by
  simpa only [nb074AlphaDummy055, nb074AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy048 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_058 :
    (nb074AlphaDummy059) ∉
      (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) 0

theorem nb074_fresh_059 :
    (nb074AlphaDummy060) ∉
      (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) 1

theorem nb074_fresh_060 :
    (nb074AlphaDummy061) ∉
      (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) 2

theorem nb074_distinct_061 : (nb074AlphaDummy059) ≠ (nb074AlphaDummy060) := by
  simpa only [nb074AlphaDummy059, nb074AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_062 : (nb074AlphaDummy059) ≠ (nb074AlphaDummy061) := by
  simpa only [nb074AlphaDummy059, nb074AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_063 : (nb074AlphaDummy060) ≠ (nb074AlphaDummy061) := by
  simpa only [nb074AlphaDummy060, nb074AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_064 (x : Var) :
    (nb074AlphaDummy062 x) ∉
      (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 0

theorem nb074_fresh_065 (x : Var) :
    (nb074AlphaDummy063 x) ∉
      (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 1

theorem nb074_fresh_066 (x : Var) :
    (nb074AlphaDummy064 x) ∉
      (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) 2

theorem nb074_distinct_067 (x : Var) :
    (nb074AlphaDummy062 x) ≠ (nb074AlphaDummy063 x) := by
  simpa only [nb074AlphaDummy062, nb074AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_068 (x : Var) :
    (nb074AlphaDummy062 x) ≠ (nb074AlphaDummy064 x) := by
  simpa only [nb074AlphaDummy062, nb074AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_069 (x : Var) :
    (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy064 x) := by
  simpa only [nb074AlphaDummy063, nb074AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_070 :
    (nb074AlphaDummy071) ∉
      (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy060))).fv) :=
  by
  simpa only [nb074AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy060))).fv)
      0

theorem nb074_fresh_071 :
    (nb074AlphaDummy067) ∉
      (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv) :=
  by
  simpa only [nb074AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv)
      0

theorem nb074_fresh_072 :
    (nb074AlphaDummy073) ∉
      (((Class.cv (nb074AlphaDummy061))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv) :=
  by
  simpa only [nb074AlphaDummy073] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy061))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv)
      0

theorem nb074_fresh_073 (x : Var) :
    (nb074AlphaDummy072 x) ∉
      (((Class.cv (nb074AlphaDummy063 x))).fv ∪ ((Class.cv (nb074AlphaDummy063 x))).fv) :=
  by
  simpa only [nb074AlphaDummy072] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy063 x))).fv ∪ ((Class.cv (nb074AlphaDummy063 x))).fv)
      0

theorem nb074_fresh_074 (x : Var) :
    (nb074AlphaDummy068 x) ∉
      (((Class.cv (nb074AlphaDummy063 x))).fv ∪ ((Class.cv (nb074AlphaDummy064 x))).fv) :=
  by
  simpa only [nb074AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy063 x))).fv ∪ ((Class.cv (nb074AlphaDummy064 x))).fv)
      0

theorem nb074_fresh_075 (x : Var) :
    (nb074AlphaDummy074 x) ∉
      (((Class.cv (nb074AlphaDummy064 x))).fv ∪ ((Class.cv (nb074AlphaDummy064 x))).fv) :=
  by
  simpa only [nb074AlphaDummy074] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy064 x))).fv ∪ ((Class.cv (nb074AlphaDummy064 x))).fv)
      0

theorem nb074_fresh_076 :
    (nb074AlphaDummy087) ∉
      (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv) :=
  by
  simpa only [nb074AlphaDummy087] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv)
      0

theorem nb074_fresh_077 :
    (nb074AlphaDummy088) ∉
      (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv) :=
  by
  simpa only [nb074AlphaDummy088] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv)
      1

theorem nb074_distinct_078 : (nb074AlphaDummy087) ≠ (nb074AlphaDummy088) := by
  simpa only [nb074AlphaDummy087, nb074AlphaDummy088] using
    (freshVar_injective
      (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_079 :
    (nb074AlphaDummy123) ∉
      (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv) :=
  by
  simpa only [nb074AlphaDummy123] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv)
      0

theorem nb074_fresh_080 :
    (nb074AlphaDummy124) ∉
      (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv) :=
  by
  simpa only [nb074AlphaDummy124] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv)
      1

theorem nb074_distinct_081 : (nb074AlphaDummy123) ≠ (nb074AlphaDummy124) := by
  simpa only [nb074AlphaDummy123, nb074AlphaDummy124] using
    (freshVar_injective
      (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_082 (x : Var) :
    (nb074AlphaDummy089 x) ∉
      (((Class.cv (nb074AlphaDummy083 x))).fv ∪ ((Class.cv (nb074AlphaDummy084 x))).fv) :=
  by
  simpa only [nb074AlphaDummy089] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy083 x))).fv ∪ ((Class.cv (nb074AlphaDummy084 x))).fv)
      0

theorem nb074_fresh_083 (x : Var) :
    (nb074AlphaDummy090 x) ∉
      (((Class.cv (nb074AlphaDummy083 x))).fv ∪ ((Class.cv (nb074AlphaDummy084 x))).fv) :=
  by
  simpa only [nb074AlphaDummy090] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy083 x))).fv ∪ ((Class.cv (nb074AlphaDummy084 x))).fv)
      1

theorem nb074_distinct_084 (x : Var) :
    (nb074AlphaDummy089 x) ≠ (nb074AlphaDummy090 x) := by
  simpa only [nb074AlphaDummy089, nb074AlphaDummy090] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy083 x))).fv ∪
        ((Class.cv (nb074AlphaDummy084 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_085 (x : Var) :
    (nb074AlphaDummy125 x) ∉
      (((Class.cv (nb074AlphaDummy084 x))).fv ∪ ((Class.cv (nb074AlphaDummy083 x))).fv) :=
  by
  simpa only [nb074AlphaDummy125] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy084 x))).fv ∪ ((Class.cv (nb074AlphaDummy083 x))).fv)
      0

theorem nb074_fresh_086 (x : Var) :
    (nb074AlphaDummy126 x) ∉
      (((Class.cv (nb074AlphaDummy084 x))).fv ∪ ((Class.cv (nb074AlphaDummy083 x))).fv) :=
  by
  simpa only [nb074AlphaDummy126] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy084 x))).fv ∪ ((Class.cv (nb074AlphaDummy083 x))).fv)
      1

theorem nb074_distinct_087 (x : Var) :
    (nb074AlphaDummy125 x) ≠ (nb074AlphaDummy126 x) := by
  simpa only [nb074AlphaDummy125, nb074AlphaDummy126] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy084 x))).fv ∪
        ((Class.cv (nb074AlphaDummy083 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_088 :
    (nb074AlphaDummy095) ∉ (((Class.cv (nb074AlphaDummy088))).fv) := by
  simpa only [nb074AlphaDummy095] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy088))).fv) 0

theorem nb074_fresh_089 :
    (nb074AlphaDummy096) ∉ (((Class.cv (nb074AlphaDummy088))).fv) := by
  simpa only [nb074AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy088))).fv) 1

theorem nb074_distinct_090 : (nb074AlphaDummy095) ≠ (nb074AlphaDummy096) := by
  simpa only [nb074AlphaDummy095, nb074AlphaDummy096] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy088))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_091 (x : Var) :
    (nb074AlphaDummy097 x) ∉ (((Class.cv (nb074AlphaDummy090 x))).fv) := by
  simpa only [nb074AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy090 x))).fv) 0

theorem nb074_fresh_092 (x : Var) :
    (nb074AlphaDummy098 x) ∉ (((Class.cv (nb074AlphaDummy090 x))).fv) := by
  simpa only [nb074AlphaDummy098] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy090 x))).fv) 1

theorem nb074_distinct_093 (x : Var) :
    (nb074AlphaDummy097 x) ≠ (nb074AlphaDummy098 x) := by
  simpa only [nb074AlphaDummy097, nb074AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy090 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_094 :
    (nb074AlphaDummy101) ∉
      (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy101] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) 0

theorem nb074_fresh_095 :
    (nb074AlphaDummy102) ∉
      (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy102] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) 1

theorem nb074_fresh_096 :
    (nb074AlphaDummy103) ∉
      (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy103] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) 2

theorem nb074_distinct_097 : (nb074AlphaDummy101) ≠ (nb074AlphaDummy102) := by
  simpa only [nb074AlphaDummy101, nb074AlphaDummy102] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_098 : (nb074AlphaDummy101) ≠ (nb074AlphaDummy103) := by
  simpa only [nb074AlphaDummy101, nb074AlphaDummy103] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_099 : (nb074AlphaDummy102) ≠ (nb074AlphaDummy103) := by
  simpa only [nb074AlphaDummy102, nb074AlphaDummy103] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_100 (x : Var) :
    (nb074AlphaDummy104 x) ∉
      (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy104] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) 0

theorem nb074_fresh_101 (x : Var) :
    (nb074AlphaDummy105 x) ∉
      (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy105] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) 1

theorem nb074_fresh_102 (x : Var) :
    (nb074AlphaDummy106 x) ∉
      (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy106] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) 2

theorem nb074_distinct_103 (x : Var) :
    (nb074AlphaDummy104 x) ≠ (nb074AlphaDummy105 x) := by
  simpa only [nb074AlphaDummy104, nb074AlphaDummy105] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_104 (x : Var) :
    (nb074AlphaDummy104 x) ≠ (nb074AlphaDummy106 x) := by
  simpa only [nb074AlphaDummy104, nb074AlphaDummy106] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_105 (x : Var) :
    (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy106 x) := by
  simpa only [nb074AlphaDummy105, nb074AlphaDummy106] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_106 :
    (nb074AlphaDummy113) ∉
      (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy102))).fv) :=
  by
  simpa only [nb074AlphaDummy113] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy102))).fv)
      0

theorem nb074_fresh_107 :
    (nb074AlphaDummy109) ∉
      (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv) :=
  by
  simpa only [nb074AlphaDummy109] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv)
      0

theorem nb074_fresh_108 :
    (nb074AlphaDummy115) ∉
      (((Class.cv (nb074AlphaDummy103))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv) :=
  by
  simpa only [nb074AlphaDummy115] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy103))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv)
      0

theorem nb074_fresh_109 (x : Var) :
    (nb074AlphaDummy114 x) ∉
      (((Class.cv (nb074AlphaDummy105 x))).fv ∪ ((Class.cv (nb074AlphaDummy105 x))).fv) :=
  by
  simpa only [nb074AlphaDummy114] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy105 x))).fv ∪ ((Class.cv (nb074AlphaDummy105 x))).fv)
      0

theorem nb074_fresh_110 (x : Var) :
    (nb074AlphaDummy110 x) ∉
      (((Class.cv (nb074AlphaDummy105 x))).fv ∪ ((Class.cv (nb074AlphaDummy106 x))).fv) :=
  by
  simpa only [nb074AlphaDummy110] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy105 x))).fv ∪ ((Class.cv (nb074AlphaDummy106 x))).fv)
      0

theorem nb074_fresh_111 (x : Var) :
    (nb074AlphaDummy116 x) ∉
      (((Class.cv (nb074AlphaDummy106 x))).fv ∪ ((Class.cv (nb074AlphaDummy106 x))).fv) :=
  by
  simpa only [nb074AlphaDummy116] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy106 x))).fv ∪ ((Class.cv (nb074AlphaDummy106 x))).fv)
      0

theorem nb074_fresh_112 :
    (nb074AlphaDummy131) ∉ (((Class.cv (nb074AlphaDummy124))).fv) := by
  simpa only [nb074AlphaDummy131] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy124))).fv) 0

theorem nb074_fresh_113 :
    (nb074AlphaDummy132) ∉ (((Class.cv (nb074AlphaDummy124))).fv) := by
  simpa only [nb074AlphaDummy132] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy124))).fv) 1

theorem nb074_distinct_114 : (nb074AlphaDummy131) ≠ (nb074AlphaDummy132) := by
  simpa only [nb074AlphaDummy131, nb074AlphaDummy132] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy124))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_115 (x : Var) :
    (nb074AlphaDummy133 x) ∉ (((Class.cv (nb074AlphaDummy126 x))).fv) := by
  simpa only [nb074AlphaDummy133] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy126 x))).fv) 0

theorem nb074_fresh_116 (x : Var) :
    (nb074AlphaDummy134 x) ∉ (((Class.cv (nb074AlphaDummy126 x))).fv) := by
  simpa only [nb074AlphaDummy134] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy126 x))).fv) 1

theorem nb074_distinct_117 (x : Var) :
    (nb074AlphaDummy133 x) ≠ (nb074AlphaDummy134 x) := by
  simpa only [nb074AlphaDummy133, nb074AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy126 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_118 :
    (nb074AlphaDummy137) ∉
      (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy137] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) 0

theorem nb074_fresh_119 :
    (nb074AlphaDummy138) ∉
      (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy138] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) 1

theorem nb074_fresh_120 :
    (nb074AlphaDummy139) ∉
      (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy139] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) 2

theorem nb074_distinct_121 : (nb074AlphaDummy137) ≠ (nb074AlphaDummy138) := by
  simpa only [nb074AlphaDummy137, nb074AlphaDummy138] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_122 : (nb074AlphaDummy137) ≠ (nb074AlphaDummy139) := by
  simpa only [nb074AlphaDummy137, nb074AlphaDummy139] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_123 : (nb074AlphaDummy138) ≠ (nb074AlphaDummy139) := by
  simpa only [nb074AlphaDummy138, nb074AlphaDummy139] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_124 (x : Var) :
    (nb074AlphaDummy140 x) ∉
      (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy140] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) 0

theorem nb074_fresh_125 (x : Var) :
    (nb074AlphaDummy141 x) ∉
      (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy141] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) 1

theorem nb074_fresh_126 (x : Var) :
    (nb074AlphaDummy142 x) ∉
      (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb074AlphaDummy142] using
    freshVar_not_mem (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) 2

theorem nb074_distinct_127 (x : Var) :
    (nb074AlphaDummy140 x) ≠ (nb074AlphaDummy141 x) := by
  simpa only [nb074AlphaDummy140, nb074AlphaDummy141] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb074_distinct_128 (x : Var) :
    (nb074AlphaDummy140 x) ≠ (nb074AlphaDummy142 x) := by
  simpa only [nb074AlphaDummy140, nb074AlphaDummy142] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb074_distinct_129 (x : Var) :
    (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy142 x) := by
  simpa only [nb074AlphaDummy141, nb074AlphaDummy142] using
    (freshVar_injective (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb074_fresh_130 :
    (nb074AlphaDummy149) ∉
      (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy138))).fv) :=
  by
  simpa only [nb074AlphaDummy149] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy138))).fv)
      0

theorem nb074_fresh_131 :
    (nb074AlphaDummy145) ∉
      (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv) :=
  by
  simpa only [nb074AlphaDummy145] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv)
      0

theorem nb074_fresh_132 :
    (nb074AlphaDummy151) ∉
      (((Class.cv (nb074AlphaDummy139))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv) :=
  by
  simpa only [nb074AlphaDummy151] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy139))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv)
      0

theorem nb074_fresh_133 (x : Var) :
    (nb074AlphaDummy150 x) ∉
      (((Class.cv (nb074AlphaDummy141 x))).fv ∪ ((Class.cv (nb074AlphaDummy141 x))).fv) :=
  by
  simpa only [nb074AlphaDummy150] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy141 x))).fv ∪ ((Class.cv (nb074AlphaDummy141 x))).fv)
      0

theorem nb074_fresh_134 (x : Var) :
    (nb074AlphaDummy146 x) ∉
      (((Class.cv (nb074AlphaDummy141 x))).fv ∪ ((Class.cv (nb074AlphaDummy142 x))).fv) :=
  by
  simpa only [nb074AlphaDummy146] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy141 x))).fv ∪ ((Class.cv (nb074AlphaDummy142 x))).fv)
      0

theorem nb074_fresh_135 (x : Var) :
    (nb074AlphaDummy152 x) ∉
      (((Class.cv (nb074AlphaDummy142 x))).fv ∪ ((Class.cv (nb074AlphaDummy142 x))).fv) :=
  by
  simpa only [nb074AlphaDummy152] using
    freshVar_not_mem
      (((Class.cv (nb074AlphaDummy142 x))).fv ∪ ((Class.cv (nb074AlphaDummy142 x))).fv)
      0

theorem nb074_fresh_136 (x : Var) : (nb074AlphaDummy083 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb074AlphaDummy083] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb074_fresh_137 (x : Var) : (nb074AlphaDummy084 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb074AlphaDummy084] using freshVar_not_mem (((Class.cv x)).fv) 1

theorem nb074_distinct_138 (x : Var) :
    (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy084 x) := by
  simpa only [nb074AlphaDummy083, nb074AlphaDummy084] using
    (freshVar_injective (((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_139 (x : Var) :
    (nb074AlphaDummy007 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) :=
  by
  simpa only [nb074AlphaDummy007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) 0

theorem nb074_fresh_140 (x : Var) :
    (nb074AlphaDummy008 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) :=
  by
  simpa only [nb074AlphaDummy008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part003`. -/


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

theorem nb074_distinct_141 (x : Var) :
    (nb074AlphaDummy007 x) ≠ (nb074AlphaDummy008 x) := by
  simpa only [nb074AlphaDummy007, nb074AlphaDummy008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb074_fresh_142 :
    (nb074AlphaDummy017) ∉
      (((Wff.classMem (Class.cv (nb074AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy013))).fv) :=
  by
  simpa only [nb074AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy013))).fv)
      0

theorem nb074_fresh_143 (x : Var) :
    (nb074AlphaDummy018 x) ∉
      (((Wff.classMem (Class.cv (nb074AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy015 x))).fv) :=
  by
  simpa only [nb074AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy015 x))).fv)
      0

theorem nb074_fresh_144 :
    (nb074AlphaDummy057) ∉
      (((Wff.classMem (Class.cv (nb074AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy053))).fv) :=
  by
  simpa only [nb074AlphaDummy057] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy053))).fv)
      0

theorem nb074_fresh_145 (x : Var) :
    (nb074AlphaDummy058 x) ∉
      (((Wff.classMem (Class.cv (nb074AlphaDummy055 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy055 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy055 x))).fv) :=
  by
  simpa only [nb074AlphaDummy058] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074AlphaDummy055 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy055 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy055 x))).fv)
      0

theorem nb074_fresh_146 :
    (nb074AlphaDummy099) ∉
      (((Wff.classMem (Class.cv (nb074AlphaDummy095)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy095)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy095))).fv) :=
  by
  simpa only [nb074AlphaDummy099] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074AlphaDummy095)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy095)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy095))).fv)
      0

theorem nb074_fresh_147 (x : Var) :
    (nb074AlphaDummy100 x) ∉
      (((Wff.classMem (Class.cv (nb074AlphaDummy097 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy097 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy097 x))).fv) :=
  by
  simpa only [nb074AlphaDummy100] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074AlphaDummy097 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy097 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy097 x))).fv)
      0

theorem nb074_fresh_148 :
    (nb074AlphaDummy135) ∉
      (((Wff.classMem (Class.cv (nb074AlphaDummy131)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy131)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy131))).fv) :=
  by
  simpa only [nb074AlphaDummy135] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074AlphaDummy131)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy131)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy131))).fv)
      0

theorem nb074_fresh_149 (x : Var) :
    (nb074AlphaDummy136 x) ∉
      (((Wff.classMem (Class.cv (nb074AlphaDummy133 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy133 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy133 x))).fv) :=
  by
  simpa only [nb074AlphaDummy136] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb074AlphaDummy133 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy133 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy133 x))).fv)
      0

theorem nb074_fresh_150 :
    (nb074AlphaDummy041) ∉
      (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb074AlphaDummy041] using
    freshVar_not_mem (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv)
      0

theorem nb074_fresh_151 :
    (nb074AlphaDummy042) ∉
      (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb074AlphaDummy042] using
    freshVar_not_mem (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv)
      1

theorem nb074_distinct_152 : (nb074AlphaDummy041) ≠ (nb074AlphaDummy042) := by
  simpa only [nb074AlphaDummy041, nb074AlphaDummy042] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb074_fresh_153 (x : Var) :
    (nb074AlphaDummy043 x) ∉ (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb074AlphaDummy043] using
    freshVar_not_mem (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv) 0

theorem nb074_fresh_154 (x : Var) :
    (nb074AlphaDummy044 x) ∉ (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb074AlphaDummy044] using
    freshVar_not_mem (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv) 1

theorem nb074_distinct_155 (x : Var) :
    (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy044 x) := by
  simpa only [nb074AlphaDummy043, nb074AlphaDummy044] using
    (freshVar_injective (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb074_fresh_156 :
    (nb074AlphaDummy009) ∉
      (((synCcompl (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCphi (Class.cv (nb074AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb074AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCphi (Class.cv (nb074AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb074_fresh_157 (x : Var) :
    (nb074AlphaDummy010 x) ∉
      (((synCcompl (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCphi (Class.cv (nb074AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb074AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCphi (Class.cv (nb074AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb074_fresh_158 :
    (nb074AlphaDummy049) ∉
      (((synCcompl (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCphi (Class.cv (nb074AlphaDummy046)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb074AlphaDummy049] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCphi (Class.cv (nb074AlphaDummy046)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb074_fresh_159 (x : Var) :
    (nb074AlphaDummy050 x) ∉
      (((synCcompl (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCphi (Class.cv (nb074AlphaDummy048 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb074AlphaDummy050] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCphi (Class.cv (nb074AlphaDummy048 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb074_fresh_160 :
    (nb074AlphaDummy091) ∉
      (((synCcompl (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCphi (Class.cv (nb074AlphaDummy088)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb074AlphaDummy091] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCphi (Class.cv (nb074AlphaDummy088)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb074_fresh_161 (x : Var) :
    (nb074AlphaDummy092 x) ∉
      (((synCcompl (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCphi (Class.cv (nb074AlphaDummy090 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb074AlphaDummy092] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCphi (Class.cv (nb074AlphaDummy090 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb074_fresh_162 :
    (nb074AlphaDummy127) ∉
      (((synCcompl (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCphi (Class.cv (nb074AlphaDummy124)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb074AlphaDummy127] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCphi (Class.cv (nb074AlphaDummy124)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb074_fresh_163 (x : Var) :
    (nb074AlphaDummy128 x) ∉
      (((synCcompl (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCphi (Class.cv (nb074AlphaDummy126 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb074AlphaDummy128] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCphi (Class.cv (nb074AlphaDummy126 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb074_fresh_164 :
    (nb074AlphaDummy029) ∉
      (((synCcompl (Class.cv (nb074AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy021)))).fv) :=
  by
  simpa only [nb074AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb074AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy021)))).fv)
      0

theorem nb074_fresh_165 (x : Var) :
    (nb074AlphaDummy030 x) ∉
      (((synCcompl (Class.cv (nb074AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy024 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb074AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy024 x)))).fv)
      0

theorem nb074_fresh_166 :
    (nb074AlphaDummy069) ∉
      (((synCcompl (Class.cv (nb074AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy061)))).fv) :=
  by
  simpa only [nb074AlphaDummy069] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb074AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy061)))).fv)
      0

theorem nb074_fresh_167 (x : Var) :
    (nb074AlphaDummy070 x) ∉
      (((synCcompl (Class.cv (nb074AlphaDummy063 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy064 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy070] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb074AlphaDummy063 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy064 x)))).fv)
      0

theorem nb074_fresh_168 :
    (nb074AlphaDummy111) ∉
      (((synCcompl (Class.cv (nb074AlphaDummy102)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy103)))).fv) :=
  by
  simpa only [nb074AlphaDummy111] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb074AlphaDummy102)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy103)))).fv)
      0

theorem nb074_fresh_169 (x : Var) :
    (nb074AlphaDummy112 x) ∉
      (((synCcompl (Class.cv (nb074AlphaDummy105 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy106 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy112] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb074AlphaDummy105 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy106 x)))).fv)
      0

theorem nb074_fresh_170 :
    (nb074AlphaDummy147) ∉
      (((synCcompl (Class.cv (nb074AlphaDummy138)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy139)))).fv) :=
  by
  simpa only [nb074AlphaDummy147] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb074AlphaDummy138)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy139)))).fv)
      0

theorem nb074_fresh_171 (x : Var) :
    (nb074AlphaDummy148 x) ∉
      (((synCcompl (Class.cv (nb074AlphaDummy141 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy142 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy148] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb074AlphaDummy141 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy142 x)))).fv)
      0

theorem nb074_fresh_172 :
    (nb074AlphaDummy037) ∉
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb074AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb074_fresh_173 (x : Var) :
    (nb074AlphaDummy038 x) ∉
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb074AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb074_fresh_174 :
    (nb074AlphaDummy077) ∉
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy046))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb074AlphaDummy077] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy046))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb074_fresh_175 (x : Var) :
    (nb074AlphaDummy078 x) ∉
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy048 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb074AlphaDummy078] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy048 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb074_fresh_176 :
    (nb074AlphaDummy119) ∉
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy088))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb074AlphaDummy119] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy088))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb074_fresh_177 (x : Var) :
    (nb074AlphaDummy120 x) ∉
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy090 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb074AlphaDummy120] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy090 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb074_fresh_178 :
    (nb074AlphaDummy155) ∉
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy124))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb074AlphaDummy155] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy124))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb074_fresh_179 (x : Var) :
    (nb074AlphaDummy156 x) ∉
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy126 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb074AlphaDummy156] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy126 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb074_fresh_180 :
    (nb074AlphaDummy025) ∉
      (((synCnin (Class.cv (nb074AlphaDummy020)) (Class.cv (nb074AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy020))
            (Class.cv (nb074AlphaDummy021)))).fv) :=
  by
  simpa only [nb074AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb074AlphaDummy020)) (Class.cv (nb074AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy020)) (Class.cv (nb074AlphaDummy021)))).fv)
      0

theorem nb074_fresh_181 (x : Var) :
    (nb074AlphaDummy026 x) ∉
      (((synCnin (Class.cv (nb074AlphaDummy023 x))
            (Class.cv (nb074AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy023 x))
            (Class.cv (nb074AlphaDummy024 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb074AlphaDummy023 x))
            (Class.cv (nb074AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy023 x))
            (Class.cv (nb074AlphaDummy024 x)))).fv)
      0

theorem nb074_fresh_182 :
    (nb074AlphaDummy065) ∉
      (((synCnin (Class.cv (nb074AlphaDummy060)) (Class.cv (nb074AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy060))
            (Class.cv (nb074AlphaDummy061)))).fv) :=
  by
  simpa only [nb074AlphaDummy065] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb074AlphaDummy060)) (Class.cv (nb074AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy060)) (Class.cv (nb074AlphaDummy061)))).fv)
      0

theorem nb074_fresh_183 (x : Var) :
    (nb074AlphaDummy066 x) ∉
      (((synCnin (Class.cv (nb074AlphaDummy063 x))
            (Class.cv (nb074AlphaDummy064 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy063 x))
            (Class.cv (nb074AlphaDummy064 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy066] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb074AlphaDummy063 x))
            (Class.cv (nb074AlphaDummy064 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy063 x))
            (Class.cv (nb074AlphaDummy064 x)))).fv)
      0

theorem nb074_fresh_184 :
    (nb074AlphaDummy107) ∉
      (((synCnin (Class.cv (nb074AlphaDummy102)) (Class.cv (nb074AlphaDummy103)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy102))
            (Class.cv (nb074AlphaDummy103)))).fv) :=
  by
  simpa only [nb074AlphaDummy107] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb074AlphaDummy102)) (Class.cv (nb074AlphaDummy103)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy102)) (Class.cv (nb074AlphaDummy103)))).fv)
      0

theorem nb074_fresh_185 (x : Var) :
    (nb074AlphaDummy108 x) ∉
      (((synCnin (Class.cv (nb074AlphaDummy105 x))
            (Class.cv (nb074AlphaDummy106 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy105 x))
            (Class.cv (nb074AlphaDummy106 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy108] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb074AlphaDummy105 x))
            (Class.cv (nb074AlphaDummy106 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy105 x))
            (Class.cv (nb074AlphaDummy106 x)))).fv)
      0

theorem nb074_fresh_186 :
    (nb074AlphaDummy143) ∉
      (((synCnin (Class.cv (nb074AlphaDummy138)) (Class.cv (nb074AlphaDummy139)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy138))
            (Class.cv (nb074AlphaDummy139)))).fv) :=
  by
  simpa only [nb074AlphaDummy143] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb074AlphaDummy138)) (Class.cv (nb074AlphaDummy139)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy138)) (Class.cv (nb074AlphaDummy139)))).fv)
      0

theorem nb074_fresh_187 (x : Var) :
    (nb074AlphaDummy144 x) ∉
      (((synCnin (Class.cv (nb074AlphaDummy141 x))
            (Class.cv (nb074AlphaDummy142 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy141 x))
            (Class.cv (nb074AlphaDummy142 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy144] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb074AlphaDummy141 x))
            (Class.cv (nb074AlphaDummy142 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy141 x))
            (Class.cv (nb074AlphaDummy142 x)))).fv)
      0

theorem nb074_fresh_188 :
    (nb074AlphaDummy039) ∉
      (((synCphi (Class.cv (nb074AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy006)))).fv) :=
  by
  simpa only [nb074AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb074AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy006)))).fv)
      0

theorem nb074_fresh_189 (x : Var) :
    (nb074AlphaDummy040 x) ∉
      (((synCphi (Class.cv (nb074AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy008 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb074AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy008 x)))).fv)
      0

theorem nb074_fresh_190 :
    (nb074AlphaDummy079) ∉
      (((synCphi (Class.cv (nb074AlphaDummy046)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy046)))).fv) :=
  by
  simpa only [nb074AlphaDummy079] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb074AlphaDummy046)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy046)))).fv)
      0

theorem nb074_fresh_191 (x : Var) :
    (nb074AlphaDummy080 x) ∉
      (((synCphi (Class.cv (nb074AlphaDummy048 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy048 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy080] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb074AlphaDummy048 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy048 x)))).fv)
      0

theorem nb074_fresh_192 :
    (nb074AlphaDummy121) ∉
      (((synCphi (Class.cv (nb074AlphaDummy088)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy088)))).fv) :=
  by
  simpa only [nb074AlphaDummy121] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb074AlphaDummy088)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy088)))).fv)
      0

theorem nb074_fresh_193 (x : Var) :
    (nb074AlphaDummy122 x) ∉
      (((synCphi (Class.cv (nb074AlphaDummy090 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy090 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy122] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb074AlphaDummy090 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy090 x)))).fv)
      0

theorem nb074_fresh_194 :
    (nb074AlphaDummy157) ∉
      (((synCphi (Class.cv (nb074AlphaDummy124)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy124)))).fv) :=
  by
  simpa only [nb074AlphaDummy157] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb074AlphaDummy124)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy124)))).fv)
      0

theorem nb074_fresh_195 (x : Var) :
    (nb074AlphaDummy158 x) ∉
      (((synCphi (Class.cv (nb074AlphaDummy126 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy126 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy158] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb074AlphaDummy126 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy126 x)))).fv)
      0

theorem nb074_fresh_196 :
    (nb074AlphaDummy001) ∉
      (({(nb074AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdm (Class.cv (nb074AlphaDummy000)))).fv) :=
  by
  simpa only [nb074AlphaDummy001] using
    freshVar_not_mem
      (({(nb074AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdm (Class.cv (nb074AlphaDummy000)))).fv)
      0

theorem nb074_fresh_197 :
    (nb074AlphaDummy003) ∉
      (({(nb074AlphaDummy000)} : Finset Var) ∪ ({(nb074AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb074AlphaDummy000)) (synCvv))
            (Wff.classEq (Class.cv (nb074AlphaDummy001))
              (synCdm (Class.cv (nb074AlphaDummy000)))))).fv) :=
  by
  simpa only [nb074AlphaDummy003] using
    freshVar_not_mem
      (({(nb074AlphaDummy000)} : Finset Var) ∪ ({(nb074AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb074AlphaDummy000)) (synCvv))
            (Wff.classEq (Class.cv (nb074AlphaDummy001))
              (synCdm (Class.cv (nb074AlphaDummy000)))))).fv)
      0

theorem nb074_fresh_198 :
    (nb074AlphaDummy085) ∉
      (({(nb074AlphaDummy081)} : Finset Var) ∪ ({(nb074AlphaDummy082)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy082)) (Class.cv (nb074AlphaDummy000))
            (Class.cv (nb074AlphaDummy081)))).fv) :=
  by
  simpa only [nb074AlphaDummy085] using
    freshVar_not_mem
      (({(nb074AlphaDummy081)} : Finset Var) ∪ ({(nb074AlphaDummy082)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy082)) (Class.cv (nb074AlphaDummy000))
            (Class.cv (nb074AlphaDummy081)))).fv)
      0

theorem nb074_fresh_199 (x : Var) :
    (nb074AlphaDummy086 x) ∉
      (({(nb074AlphaDummy083 x)} : Finset Var) ∪ ({(nb074AlphaDummy084 x)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy084 x)) (Class.cv x)
            (Class.cv (nb074AlphaDummy083 x)))).fv) :=
  by
  simpa only [nb074AlphaDummy086] using
    freshVar_not_mem
      (({(nb074AlphaDummy083 x)} : Finset Var) ∪ ({(nb074AlphaDummy084 x)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy084 x)) (Class.cv x)
            (Class.cv (nb074AlphaDummy083 x)))).fv)
      0

theorem nb074_fresh_200 (x : Var) :
    (nb074AlphaDummy002 x) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCdm (Class.cv x))).fv) :=
  by
  simpa only [nb074AlphaDummy002] using
    freshVar_not_mem (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCdm (Class.cv x))).fv)
      0

theorem nb074_fresh_201 (x : Var) :
    (nb074AlphaDummy004 x) ∉
      (({ x } : Finset Var) ∪ ({(nb074AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb074AlphaDummy002 x)) (synCdm (Class.cv x))))).fv) :=
  by
  simpa only [nb074AlphaDummy004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb074AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb074AlphaDummy002 x)) (synCdm (Class.cv x))))).fv)
      0

theorem nb074_fresh_202 : (nb074AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb074AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb074_support_mem_0000 :
    (nb074AlphaDummy000) ∈
      (({(nb074AlphaDummy000)} : Finset Var) ∪ ({(nb074AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb074AlphaDummy000)) (synCvv))
            (Wff.classEq (Class.cv (nb074AlphaDummy001))
              (synCdm (Class.cv (nb074AlphaDummy000)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0001 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb074AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb074AlphaDummy002 x)) (synCdm (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0002 :
    (nb074AlphaDummy001) ∈
      (({(nb074AlphaDummy000)} : Finset Var) ∪ ({(nb074AlphaDummy001)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb074AlphaDummy000)) (synCvv))
            (Wff.classEq (Class.cv (nb074AlphaDummy001))
              (synCdm (Class.cv (nb074AlphaDummy000)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0003 (x : Var) :
    (nb074AlphaDummy002 x) ∈
      (({ x } : Finset Var) ∪ ({(nb074AlphaDummy002 x)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv x) (synCvv))
            (Wff.classEq (Class.cv (nb074AlphaDummy002 x)) (synCdm (Class.cv x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0004 :
    (nb074AlphaDummy000) ∈
      (({(nb074AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdm (Class.cv (nb074AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0005 (x : Var) :
    x ∈ (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ((synCdm (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0006 :
    (nb074AlphaDummy000) ∈
      (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0007 :
    (nb074AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCphi (Class.cv (nb074AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy005) from (by
          unfold nb074AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy006) from (by
            unfold nb074AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0008 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0009 (x : Var) :
    x ∈
      (((synCcompl (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCphi (Class.cv (nb074AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb074AlphaDummy007 x) from (by
          unfold nb074AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb074AlphaDummy008 x) from (by
            unfold nb074AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0010 :
    (nb074AlphaDummy000) ∈
      (((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCphi (Class.cv (nb074AlphaDummy006))))))).fv ∪
        ((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCphi (Class.cv (nb074AlphaDummy006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy005) from (by
          unfold nb074AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy006) from (by
            unfold nb074AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0011 (x : Var) :
    x ∈
      (((Class.cab (nb074AlphaDummy007 x) (synWrex (nb074AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCphi (Class.cv (nb074AlphaDummy008 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy007 x) (synWrex (nb074AlphaDummy008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCphi (Class.cv (nb074AlphaDummy008 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb074AlphaDummy007 x) from (by
          unfold nb074AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb074AlphaDummy008 x) from (by
            unfold nb074AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0012 :
    (nb074AlphaDummy006) ∈ (((Class.cv (nb074AlphaDummy006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0013 (x : Var) :
    (nb074AlphaDummy008 x) ∈ (((Class.cv (nb074AlphaDummy008 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0014 :
    (nb074AlphaDummy013) ∈
      (((Wff.classMem (Class.cv (nb074AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy013))).fv) :=
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

theorem nb074_support_mem_0015 (x : Var) :
    (nb074AlphaDummy015 x) ∈
      (((Wff.classMem (Class.cv (nb074AlphaDummy015 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy015 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy015 x))).fv) :=
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

theorem nb074_support_mem_0016 :
    (nb074AlphaDummy013) ∈
      (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0017 (x : Var) :
    (nb074AlphaDummy015 x) ∈
      (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0018 :
    (nb074AlphaDummy020) ∈
      (((synCnin (Class.cv (nb074AlphaDummy020)) (Class.cv (nb074AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy020))
            (Class.cv (nb074AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0019 (x : Var) :
    (nb074AlphaDummy023 x) ∈
      (((synCnin (Class.cv (nb074AlphaDummy023 x))
            (Class.cv (nb074AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy023 x))
            (Class.cv (nb074AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0020 :
    (nb074AlphaDummy020) ∈
      (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0021 (x : Var) :
    (nb074AlphaDummy023 x) ∈
      (((Class.cv (nb074AlphaDummy023 x))).fv ∪ ((Class.cv (nb074AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0022 :
    (nb074AlphaDummy021) ∈
      (((synCnin (Class.cv (nb074AlphaDummy020)) (Class.cv (nb074AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy020))
            (Class.cv (nb074AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0023 (x : Var) :
    (nb074AlphaDummy024 x) ∈
      (((synCnin (Class.cv (nb074AlphaDummy023 x))
            (Class.cv (nb074AlphaDummy024 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy023 x))
            (Class.cv (nb074AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0024 :
    (nb074AlphaDummy021) ∈
      (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0025 (x : Var) :
    (nb074AlphaDummy024 x) ∈
      (((Class.cv (nb074AlphaDummy023 x))).fv ∪ ((Class.cv (nb074AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0026 :
    (nb074AlphaDummy020) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0027 (x : Var) :
    (nb074AlphaDummy023 x) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0028 :
    (nb074AlphaDummy020) ∈
      (((Class.cv (nb074AlphaDummy020))).fv ∪ ((Class.cv (nb074AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0029 (x : Var) :
    (nb074AlphaDummy023 x) ∈
      (((Class.cv (nb074AlphaDummy023 x))).fv ∪ ((Class.cv (nb074AlphaDummy023 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0030 :
    (nb074AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0031 (x : Var) :
    (nb074AlphaDummy024 x) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0032 :
    (nb074AlphaDummy021) ∈
      (((Class.cv (nb074AlphaDummy021))).fv ∪ ((Class.cv (nb074AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0033 (x : Var) :
    (nb074AlphaDummy024 x) ∈
      (((Class.cv (nb074AlphaDummy024 x))).fv ∪ ((Class.cv (nb074AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0034 :
    (nb074AlphaDummy001) ∈
      (((Class.cv (nb074AlphaDummy000))).fv ∪ ((Class.cv (nb074AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0035 :
    (nb074AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy000))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCphi (Class.cv (nb074AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy005) from (by
          unfold nb074AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy006) from (by
            unfold nb074AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0036 (x : Var) :
    (nb074AlphaDummy002 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0037 (x : Var) :
    (nb074AlphaDummy002 x) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCphi (Class.cv (nb074AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy007 x) from (by
          unfold nb074AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy008 x) from (by
            unfold nb074AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0038 :
    (nb074AlphaDummy001) ∈
      (((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy005) from (by
          unfold nb074AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy006) from (by
            unfold nb074AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0039 (x : Var) :
    (nb074AlphaDummy002 x) ∈
      (((Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy007 x) from (by
          unfold nb074AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy008 x) from (by
            unfold nb074AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0040 :
    (nb074AlphaDummy006) ∈
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0041 (x : Var) :
    (nb074AlphaDummy008 x) ∈
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0042 :
    (nb074AlphaDummy006) ∈
      (((synCphi (Class.cv (nb074AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0043 (x : Var) :
    (nb074AlphaDummy008 x) ∈
      (((synCphi (Class.cv (nb074AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy008 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0044 :
    (nb074AlphaDummy042) ∈
      (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0045 :
    (nb074AlphaDummy042) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCphi (Class.cv (nb074AlphaDummy046)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy045) from (by
          unfold nb074AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy046) from (by
            unfold nb074AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0046 (x : Var) :
    (nb074AlphaDummy044 x) ∈
      (((Class.cv (nb074AlphaDummy044 x))).fv ∪ ((Class.cv (nb074AlphaDummy043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0047 (x : Var) :
    (nb074AlphaDummy044 x) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCphi (Class.cv (nb074AlphaDummy048 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy047 x) from (by
          unfold nb074AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy048 x) from (by
            unfold nb074AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0048 :
    (nb074AlphaDummy042) ∈
      (((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCphi (Class.cv (nb074AlphaDummy046))))))).fv ∪
        ((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCphi (Class.cv (nb074AlphaDummy046))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy045) from (by
          unfold nb074AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy046) from (by
            unfold nb074AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0049 (x : Var) :
    (nb074AlphaDummy044 x) ∈
      (((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCphi (Class.cv (nb074AlphaDummy048 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCphi (Class.cv (nb074AlphaDummy048 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy047 x) from (by
          unfold nb074AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy048 x) from (by
            unfold nb074AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0050 :
    (nb074AlphaDummy046) ∈ (((Class.cv (nb074AlphaDummy046))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0051 (x : Var) :
    (nb074AlphaDummy048 x) ∈ (((Class.cv (nb074AlphaDummy048 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0052 :
    (nb074AlphaDummy053) ∈
      (((Wff.classMem (Class.cv (nb074AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy053))).fv) :=
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

theorem nb074_support_mem_0053 (x : Var) :
    (nb074AlphaDummy055 x) ∈
      (((Wff.classMem (Class.cv (nb074AlphaDummy055 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy055 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy055 x))).fv) :=
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

theorem nb074_support_mem_0054 :
    (nb074AlphaDummy053) ∈
      (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0055 (x : Var) :
    (nb074AlphaDummy055 x) ∈
      (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0056 :
    (nb074AlphaDummy060) ∈
      (((synCnin (Class.cv (nb074AlphaDummy060)) (Class.cv (nb074AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy060))
            (Class.cv (nb074AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0057 (x : Var) :
    (nb074AlphaDummy063 x) ∈
      (((synCnin (Class.cv (nb074AlphaDummy063 x))
            (Class.cv (nb074AlphaDummy064 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy063 x))
            (Class.cv (nb074AlphaDummy064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0058 :
    (nb074AlphaDummy060) ∈
      (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0059 (x : Var) :
    (nb074AlphaDummy063 x) ∈
      (((Class.cv (nb074AlphaDummy063 x))).fv ∪ ((Class.cv (nb074AlphaDummy064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0060 :
    (nb074AlphaDummy061) ∈
      (((synCnin (Class.cv (nb074AlphaDummy060)) (Class.cv (nb074AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy060))
            (Class.cv (nb074AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0061 (x : Var) :
    (nb074AlphaDummy064 x) ∈
      (((synCnin (Class.cv (nb074AlphaDummy063 x))
            (Class.cv (nb074AlphaDummy064 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy063 x))
            (Class.cv (nb074AlphaDummy064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0062 :
    (nb074AlphaDummy061) ∈
      (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0063 (x : Var) :
    (nb074AlphaDummy064 x) ∈
      (((Class.cv (nb074AlphaDummy063 x))).fv ∪ ((Class.cv (nb074AlphaDummy064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0064 :
    (nb074AlphaDummy060) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0065 (x : Var) :
    (nb074AlphaDummy063 x) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy063 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0066 :
    (nb074AlphaDummy060) ∈
      (((Class.cv (nb074AlphaDummy060))).fv ∪ ((Class.cv (nb074AlphaDummy060))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0067 (x : Var) :
    (nb074AlphaDummy063 x) ∈
      (((Class.cv (nb074AlphaDummy063 x))).fv ∪ ((Class.cv (nb074AlphaDummy063 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0068 :
    (nb074AlphaDummy061) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0069 (x : Var) :
    (nb074AlphaDummy064 x) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy063 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy064 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0070 :
    (nb074AlphaDummy061) ∈
      (((Class.cv (nb074AlphaDummy061))).fv ∪ ((Class.cv (nb074AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0071 (x : Var) :
    (nb074AlphaDummy064 x) ∈
      (((Class.cv (nb074AlphaDummy064 x))).fv ∪ ((Class.cv (nb074AlphaDummy064 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0072 :
    (nb074AlphaDummy041) ∈
      (((Class.cv (nb074AlphaDummy042))).fv ∪ ((Class.cv (nb074AlphaDummy041))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0073 :
    (nb074AlphaDummy041) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCphi (Class.cv (nb074AlphaDummy046)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy041) ≠ (nb074AlphaDummy045) from (by
          unfold nb074AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy041) ≠ (nb074AlphaDummy046) from (by
            unfold nb074AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0074 (x : Var) :
    (nb074AlphaDummy043 x) ∈
      (((Class.cv (nb074AlphaDummy044 x))).fv ∪ ((Class.cv (nb074AlphaDummy043 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part004`. -/


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

theorem nb074_support_mem_0075 (x : Var) :
    (nb074AlphaDummy043 x) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCphi (Class.cv (nb074AlphaDummy048 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy047 x) from (by
          unfold nb074AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy048 x) from (by
            unfold nb074AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0076 :
    (nb074AlphaDummy041) ∈
      (((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy045)
            (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
              (Wff.classEq (Class.cv (nb074AlphaDummy045))
                (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy041) ≠ (nb074AlphaDummy045) from (by
          unfold nb074AlphaDummy045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy041) ≠ (nb074AlphaDummy046) from (by
            unfold nb074AlphaDummy046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0077 (x : Var) :
    (nb074AlphaDummy043 x) ∈
      (((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy047 x)
            (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy047 x) from (by
          unfold nb074AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy048 x) from (by
            unfold nb074AlphaDummy048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0078 :
    (nb074AlphaDummy046) ∈
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy046))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0079 (x : Var) :
    (nb074AlphaDummy048 x) ∈
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy048 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0080 :
    (nb074AlphaDummy046) ∈
      (((synCphi (Class.cv (nb074AlphaDummy046)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy046)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0081 (x : Var) :
    (nb074AlphaDummy048 x) ∈
      (((synCphi (Class.cv (nb074AlphaDummy048 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy048 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0082 :
    (nb074AlphaDummy081) ∈
      (({(nb074AlphaDummy081)} : Finset Var) ∪ ({(nb074AlphaDummy082)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy082)) (Class.cv (nb074AlphaDummy000))
            (Class.cv (nb074AlphaDummy081)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0083 (x : Var) :
    (nb074AlphaDummy083 x) ∈
      (({(nb074AlphaDummy083 x)} : Finset Var) ∪ ({(nb074AlphaDummy084 x)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy084 x)) (Class.cv x)
            (Class.cv (nb074AlphaDummy083 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0084 :
    (nb074AlphaDummy082) ∈
      (({(nb074AlphaDummy081)} : Finset Var) ∪ ({(nb074AlphaDummy082)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy082)) (Class.cv (nb074AlphaDummy000))
            (Class.cv (nb074AlphaDummy081)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0085 (x : Var) :
    (nb074AlphaDummy084 x) ∈
      (({(nb074AlphaDummy083 x)} : Finset Var) ∪ ({(nb074AlphaDummy084 x)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy084 x)) (Class.cv x)
            (Class.cv (nb074AlphaDummy083 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0086 :
    (nb074AlphaDummy081) ∈
      (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0087 :
    (nb074AlphaDummy081) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCphi (Class.cv (nb074AlphaDummy088)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy087) from (by
          unfold nb074AlphaDummy087;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy088) from (by
            unfold nb074AlphaDummy088;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0088 (x : Var) :
    (nb074AlphaDummy083 x) ∈
      (((Class.cv (nb074AlphaDummy083 x))).fv ∪ ((Class.cv (nb074AlphaDummy084 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0089 (x : Var) :
    (nb074AlphaDummy083 x) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCphi (Class.cv (nb074AlphaDummy090 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy089 x) from (by
          unfold nb074AlphaDummy089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy090 x) from (by
            unfold nb074AlphaDummy090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0090 :
    (nb074AlphaDummy081) ∈
      (((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCphi (Class.cv (nb074AlphaDummy088))))))).fv ∪
        ((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCphi (Class.cv (nb074AlphaDummy088))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy087) from (by
          unfold nb074AlphaDummy087;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy088) from (by
            unfold nb074AlphaDummy088;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0091 (x : Var) :
    (nb074AlphaDummy083 x) ∈
      (((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCphi (Class.cv (nb074AlphaDummy090 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCphi (Class.cv (nb074AlphaDummy090 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy089 x) from (by
          unfold nb074AlphaDummy089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy090 x) from (by
            unfold nb074AlphaDummy090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0092 :
    (nb074AlphaDummy088) ∈ (((Class.cv (nb074AlphaDummy088))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0093 (x : Var) :
    (nb074AlphaDummy090 x) ∈ (((Class.cv (nb074AlphaDummy090 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0094 :
    (nb074AlphaDummy095) ∈
      (((Wff.classMem (Class.cv (nb074AlphaDummy095)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy095)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy095))).fv) :=
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

theorem nb074_support_mem_0095 (x : Var) :
    (nb074AlphaDummy097 x) ∈
      (((Wff.classMem (Class.cv (nb074AlphaDummy097 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy097 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy097 x))).fv) :=
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

theorem nb074_support_mem_0096 :
    (nb074AlphaDummy095) ∈
      (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0097 (x : Var) :
    (nb074AlphaDummy097 x) ∈
      (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0098 :
    (nb074AlphaDummy102) ∈
      (((synCnin (Class.cv (nb074AlphaDummy102)) (Class.cv (nb074AlphaDummy103)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy102))
            (Class.cv (nb074AlphaDummy103)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0099 (x : Var) :
    (nb074AlphaDummy105 x) ∈
      (((synCnin (Class.cv (nb074AlphaDummy105 x))
            (Class.cv (nb074AlphaDummy106 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy105 x))
            (Class.cv (nb074AlphaDummy106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0100 :
    (nb074AlphaDummy102) ∈
      (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0101 (x : Var) :
    (nb074AlphaDummy105 x) ∈
      (((Class.cv (nb074AlphaDummy105 x))).fv ∪ ((Class.cv (nb074AlphaDummy106 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0102 :
    (nb074AlphaDummy103) ∈
      (((synCnin (Class.cv (nb074AlphaDummy102)) (Class.cv (nb074AlphaDummy103)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy102))
            (Class.cv (nb074AlphaDummy103)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0103 (x : Var) :
    (nb074AlphaDummy106 x) ∈
      (((synCnin (Class.cv (nb074AlphaDummy105 x))
            (Class.cv (nb074AlphaDummy106 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy105 x))
            (Class.cv (nb074AlphaDummy106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0104 :
    (nb074AlphaDummy103) ∈
      (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0105 (x : Var) :
    (nb074AlphaDummy106 x) ∈
      (((Class.cv (nb074AlphaDummy105 x))).fv ∪ ((Class.cv (nb074AlphaDummy106 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0106 :
    (nb074AlphaDummy102) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy102)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy103)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0107 (x : Var) :
    (nb074AlphaDummy105 x) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy105 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0108 :
    (nb074AlphaDummy102) ∈
      (((Class.cv (nb074AlphaDummy102))).fv ∪ ((Class.cv (nb074AlphaDummy102))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0109 (x : Var) :
    (nb074AlphaDummy105 x) ∈
      (((Class.cv (nb074AlphaDummy105 x))).fv ∪ ((Class.cv (nb074AlphaDummy105 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0110 :
    (nb074AlphaDummy103) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy102)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy103)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0111 (x : Var) :
    (nb074AlphaDummy106 x) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy105 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy106 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0112 :
    (nb074AlphaDummy103) ∈
      (((Class.cv (nb074AlphaDummy103))).fv ∪ ((Class.cv (nb074AlphaDummy103))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0113 (x : Var) :
    (nb074AlphaDummy106 x) ∈
      (((Class.cv (nb074AlphaDummy106 x))).fv ∪ ((Class.cv (nb074AlphaDummy106 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0114 :
    (nb074AlphaDummy082) ∈
      (((Class.cv (nb074AlphaDummy081))).fv ∪ ((Class.cv (nb074AlphaDummy082))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0115 :
    (nb074AlphaDummy082) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCphi (Class.cv (nb074AlphaDummy088)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy087) from (by
          unfold nb074AlphaDummy087;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy088) from (by
            unfold nb074AlphaDummy088;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0116 (x : Var) :
    (nb074AlphaDummy084 x) ∈
      (((Class.cv (nb074AlphaDummy083 x))).fv ∪ ((Class.cv (nb074AlphaDummy084 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0117 (x : Var) :
    (nb074AlphaDummy084 x) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCphi (Class.cv (nb074AlphaDummy090 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy089 x) from (by
          unfold nb074AlphaDummy089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy090 x) from (by
            unfold nb074AlphaDummy090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0118 :
    (nb074AlphaDummy082) ∈
      (((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCun (synCphi (Class.cv (nb074AlphaDummy088)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy087) from (by
          unfold nb074AlphaDummy087;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy088) from (by
            unfold nb074AlphaDummy088;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0119 (x : Var) :
    (nb074AlphaDummy084 x) ∈
      (((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy090 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy089 x) from (by
          unfold nb074AlphaDummy089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy090 x) from (by
            unfold nb074AlphaDummy090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0120 :
    (nb074AlphaDummy088) ∈
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy088))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0121 (x : Var) :
    (nb074AlphaDummy090 x) ∈
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy090 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0122 :
    (nb074AlphaDummy088) ∈
      (((synCphi (Class.cv (nb074AlphaDummy088)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy088)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0123 (x : Var) :
    (nb074AlphaDummy090 x) ∈
      (((synCphi (Class.cv (nb074AlphaDummy090 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0124 :
    (nb074AlphaDummy082) ∈
      (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0125 :
    (nb074AlphaDummy082) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCphi (Class.cv (nb074AlphaDummy124)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy123) from (by
          unfold nb074AlphaDummy123;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy124) from (by
            unfold nb074AlphaDummy124;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0126 (x : Var) :
    (nb074AlphaDummy084 x) ∈
      (((Class.cv (nb074AlphaDummy084 x))).fv ∪ ((Class.cv (nb074AlphaDummy083 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0127 (x : Var) :
    (nb074AlphaDummy084 x) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCphi (Class.cv (nb074AlphaDummy126 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy125 x) from (by
          unfold nb074AlphaDummy125;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy126 x) from (by
            unfold nb074AlphaDummy126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0128 :
    (nb074AlphaDummy082) ∈
      (((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCphi (Class.cv (nb074AlphaDummy124))))))).fv ∪
        ((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCphi (Class.cv (nb074AlphaDummy124))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy123) from (by
          unfold nb074AlphaDummy123;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy124) from (by
            unfold nb074AlphaDummy124;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0129 (x : Var) :
    (nb074AlphaDummy084 x) ∈
      (((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCphi (Class.cv (nb074AlphaDummy126 x))))))).fv ∪
        ((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCphi (Class.cv (nb074AlphaDummy126 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy125 x) from (by
          unfold nb074AlphaDummy125;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy126 x) from (by
            unfold nb074AlphaDummy126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0130 :
    (nb074AlphaDummy124) ∈ (((Class.cv (nb074AlphaDummy124))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0131 (x : Var) :
    (nb074AlphaDummy126 x) ∈ (((Class.cv (nb074AlphaDummy126 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0132 :
    (nb074AlphaDummy131) ∈
      (((Wff.classMem (Class.cv (nb074AlphaDummy131)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy131)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy131))).fv) :=
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

theorem nb074_support_mem_0133 (x : Var) :
    (nb074AlphaDummy133 x) ∈
      (((Wff.classMem (Class.cv (nb074AlphaDummy133 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb074AlphaDummy133 x)) (synC1c))).fv ∪
        ((Class.cv (nb074AlphaDummy133 x))).fv) :=
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

theorem nb074_support_mem_0134 :
    (nb074AlphaDummy131) ∈
      (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0135 (x : Var) :
    (nb074AlphaDummy133 x) ∈
      (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0136 :
    (nb074AlphaDummy138) ∈
      (((synCnin (Class.cv (nb074AlphaDummy138)) (Class.cv (nb074AlphaDummy139)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy138))
            (Class.cv (nb074AlphaDummy139)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0137 (x : Var) :
    (nb074AlphaDummy141 x) ∈
      (((synCnin (Class.cv (nb074AlphaDummy141 x))
            (Class.cv (nb074AlphaDummy142 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy141 x))
            (Class.cv (nb074AlphaDummy142 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0138 :
    (nb074AlphaDummy138) ∈
      (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0139 (x : Var) :
    (nb074AlphaDummy141 x) ∈
      (((Class.cv (nb074AlphaDummy141 x))).fv ∪ ((Class.cv (nb074AlphaDummy142 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0140 :
    (nb074AlphaDummy139) ∈
      (((synCnin (Class.cv (nb074AlphaDummy138)) (Class.cv (nb074AlphaDummy139)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy138))
            (Class.cv (nb074AlphaDummy139)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0141 (x : Var) :
    (nb074AlphaDummy142 x) ∈
      (((synCnin (Class.cv (nb074AlphaDummy141 x))
            (Class.cv (nb074AlphaDummy142 x)))).fv ∪
        ((synCnin (Class.cv (nb074AlphaDummy141 x))
            (Class.cv (nb074AlphaDummy142 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0142 :
    (nb074AlphaDummy139) ∈
      (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0143 (x : Var) :
    (nb074AlphaDummy142 x) ∈
      (((Class.cv (nb074AlphaDummy141 x))).fv ∪ ((Class.cv (nb074AlphaDummy142 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0144 :
    (nb074AlphaDummy138) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy138)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy139)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0145 (x : Var) :
    (nb074AlphaDummy141 x) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy141 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy142 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0146 :
    (nb074AlphaDummy138) ∈
      (((Class.cv (nb074AlphaDummy138))).fv ∪ ((Class.cv (nb074AlphaDummy138))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0147 (x : Var) :
    (nb074AlphaDummy141 x) ∈
      (((Class.cv (nb074AlphaDummy141 x))).fv ∪ ((Class.cv (nb074AlphaDummy141 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0148 :
    (nb074AlphaDummy139) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy138)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy139)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0149 (x : Var) :
    (nb074AlphaDummy142 x) ∈
      (((synCcompl (Class.cv (nb074AlphaDummy141 x)))).fv ∪
        ((synCcompl (Class.cv (nb074AlphaDummy142 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0150 :
    (nb074AlphaDummy139) ∈
      (((Class.cv (nb074AlphaDummy139))).fv ∪ ((Class.cv (nb074AlphaDummy139))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0151 (x : Var) :
    (nb074AlphaDummy142 x) ∈
      (((Class.cv (nb074AlphaDummy142 x))).fv ∪ ((Class.cv (nb074AlphaDummy142 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0152 :
    (nb074AlphaDummy081) ∈
      (((Class.cv (nb074AlphaDummy082))).fv ∪ ((Class.cv (nb074AlphaDummy081))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0153 :
    (nb074AlphaDummy081) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCphi (Class.cv (nb074AlphaDummy124)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy123) from (by
          unfold nb074AlphaDummy123;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy124) from (by
            unfold nb074AlphaDummy124;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0154 (x : Var) :
    (nb074AlphaDummy083 x) ∈
      (((Class.cv (nb074AlphaDummy084 x))).fv ∪ ((Class.cv (nb074AlphaDummy083 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0155 (x : Var) :
    (nb074AlphaDummy083 x) ∈
      (((synCcompl (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCphi (Class.cv (nb074AlphaDummy126 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy125 x) from (by
          unfold nb074AlphaDummy125;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy126 x) from (by
            unfold nb074AlphaDummy126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0156 :
    (nb074AlphaDummy081) ∈
      (((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCun (synCphi (Class.cv (nb074AlphaDummy124)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy123) from (by
          unfold nb074AlphaDummy123;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy124) from (by
            unfold nb074AlphaDummy124;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0157 (x : Var) :
    (nb074AlphaDummy083 x) ∈
      (((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy126 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy125 x) from (by
          unfold nb074AlphaDummy125;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy126 x) from (by
            unfold nb074AlphaDummy126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0158 :
    (nb074AlphaDummy124) ∈
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy124))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0159 (x : Var) :
    (nb074AlphaDummy126 x) ∈
      (((synCcompl (synCphi (Class.cv (nb074AlphaDummy126 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0160 :
    (nb074AlphaDummy124) ∈
      (((synCphi (Class.cv (nb074AlphaDummy124)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy124)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0161 (x : Var) :
    (nb074AlphaDummy126 x) ∈
      (((synCphi (Class.cv (nb074AlphaDummy126 x)))).fv ∪
        ((synCphi (Class.cv (nb074AlphaDummy126 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0162 :
    (nb074AlphaDummy000) ∈
      (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0163 (x : Var) :
    x ∈ (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0164 :
    (nb074AlphaDummy000) ∈
      (({(nb074AlphaDummy081)} : Finset Var) ∪ ({(nb074AlphaDummy082)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy082)) (Class.cv (nb074AlphaDummy000))
            (Class.cv (nb074AlphaDummy081)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0165 (x : Var) :
    x ∈
      (({(nb074AlphaDummy083 x)} : Finset Var) ∪ ({(nb074AlphaDummy084 x)} : Finset Var) ∪
        ((synWbr (Class.cv (nb074AlphaDummy084 x)) (Class.cv x)
            (Class.cv (nb074AlphaDummy083 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0166 :
    (nb074AlphaDummy000) ∈ (((Class.cv (nb074AlphaDummy000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0167 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
