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

/-! Certificates from `NAR4C078C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_000`. -/
@[expose]
noncomputable def nb078AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_001`. -/
@[expose]
noncomputable def nb078AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_002`. -/
@[expose]
noncomputable def nb078AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_003`. -/
@[expose]
noncomputable def nb078AlphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_004`. -/
@[expose]
noncomputable def nb078AlphaDummy004 : Var :=
  (freshVar ((∅ : Finset Var)) 4)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_005`. -/
@[expose]
noncomputable def nb078AlphaDummy005 : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb078AlphaDummy000))
            (synCcnv (Class.cv (nb078AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
          (synCcom (Class.cv (nb078AlphaDummy000))
            (synCcnv (Class.cv (nb078AlphaDummy000)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_006`. -/
@[expose]
noncomputable def nb078AlphaDummy006 (f : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_007`. -/
@[expose]
noncomputable def nb078AlphaDummy007 : Var :=
  (freshVar (((synCcom (Class.cv (nb078AlphaDummy000))
          (synCcnv (Class.cv (nb078AlphaDummy000))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_008`. -/
@[expose]
noncomputable def nb078AlphaDummy008 (f : Var) : Var :=
  (freshVar (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_009`. -/
@[expose]
noncomputable def nb078AlphaDummy009 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_010`. -/
@[expose]
noncomputable def nb078AlphaDummy010 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_011`. -/
@[expose]
noncomputable def nb078AlphaDummy011 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_012`. -/
@[expose]
noncomputable def nb078AlphaDummy012 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_013`. -/
@[expose]
noncomputable def nb078AlphaDummy013 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_014`. -/
@[expose]
noncomputable def nb078AlphaDummy014 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_015`. -/
@[expose]
noncomputable def nb078AlphaDummy015 : Var :=
  (freshVar
    (({(nb078AlphaDummy009)} : Finset Var) ∪ ({(nb078AlphaDummy010)} : Finset Var) ∪
      ((synWex (nb078AlphaDummy011) (synWa (synWbr (Class.cv (nb078AlphaDummy009))
              (synCcnv (Class.cv (nb078AlphaDummy000))) (Class.cv (nb078AlphaDummy011)))
            (synWbr (Class.cv (nb078AlphaDummy011)) (Class.cv (nb078AlphaDummy000))
              (Class.cv (nb078AlphaDummy010)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_016`. -/
@[expose]
noncomputable def nb078AlphaDummy016 (f : Var) : Var :=
  (freshVar (({(nb078AlphaDummy012 f)} : Finset Var) ∪
        ({(nb078AlphaDummy013 f)} : Finset Var) ∪ ((synWex (nb078AlphaDummy014 f) (synWa
            (synWbr (Class.cv (nb078AlphaDummy012 f)) (synCcnv (Class.cv f))
              (Class.cv (nb078AlphaDummy014 f)))
            (synWbr (Class.cv (nb078AlphaDummy014 f)) (Class.cv f)
              (Class.cv (nb078AlphaDummy013 f)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_017`. -/
@[expose]
noncomputable def nb078AlphaDummy017 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_018`. -/
@[expose]
noncomputable def nb078AlphaDummy018 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_019`. -/
@[expose]
noncomputable def nb078AlphaDummy019 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy012 f))).fv ∪
      ((Class.cv (nb078AlphaDummy013 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_020`. -/
@[expose]
noncomputable def nb078AlphaDummy020 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy012 f))).fv ∪
      ((Class.cv (nb078AlphaDummy013 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_021`. -/
@[expose]
noncomputable def nb078AlphaDummy021 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCphi (Class.cv (nb078AlphaDummy018)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_022`. -/
@[expose]
noncomputable def nb078AlphaDummy022 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCphi (Class.cv (nb078AlphaDummy020 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_023`. -/
@[expose]
noncomputable def nb078AlphaDummy023 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy017)
          (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
            (Wff.classEq (Class.cv (nb078AlphaDummy017))
              (synCphi (Class.cv (nb078AlphaDummy018))))))).fv ∪
      ((Class.cab (nb078AlphaDummy017)
          (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
            (Wff.classEq (Class.cv (nb078AlphaDummy017))
              (synCphi (Class.cv (nb078AlphaDummy018))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_024`. -/
@[expose]
noncomputable def nb078AlphaDummy024 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy019 f)
          (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
              (synCphi (Class.cv (nb078AlphaDummy020 f))))))).fv ∪
      ((Class.cab (nb078AlphaDummy019 f)
          (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
              (synCphi (Class.cv (nb078AlphaDummy020 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_025`. -/
@[expose]
noncomputable def nb078AlphaDummy025 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy018))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_026`. -/
@[expose]
noncomputable def nb078AlphaDummy026 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy018))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_027`. -/
@[expose]
noncomputable def nb078AlphaDummy027 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy020 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_028`. -/
@[expose]
noncomputable def nb078AlphaDummy028 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy020 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_029`. -/
@[expose]
noncomputable def nb078AlphaDummy029 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy025)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy025)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy025))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_030`. -/
@[expose]
noncomputable def nb078AlphaDummy030 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy027 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy027 f)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy027 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_031`. -/
@[expose]
noncomputable def nb078AlphaDummy031 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_032`. -/
@[expose]
noncomputable def nb078AlphaDummy032 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_033`. -/
@[expose]
noncomputable def nb078AlphaDummy033 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_034`. -/
@[expose]
noncomputable def nb078AlphaDummy034 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_035`. -/
@[expose]
noncomputable def nb078AlphaDummy035 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_036`. -/
@[expose]
noncomputable def nb078AlphaDummy036 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_037`. -/
@[expose]
noncomputable def nb078AlphaDummy037 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy032))
          (Class.cv (nb078AlphaDummy033)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy032)) (Class.cv (nb078AlphaDummy033)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_038`. -/
@[expose]
noncomputable def nb078AlphaDummy038 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy035 f))
          (Class.cv (nb078AlphaDummy036 f)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy035 f)) (Class.cv (nb078AlphaDummy036 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_039`. -/
@[expose]
noncomputable def nb078AlphaDummy039 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_040`. -/
@[expose]
noncomputable def nb078AlphaDummy040 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy035 f))).fv ∪
      ((Class.cv (nb078AlphaDummy036 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_041`. -/
@[expose]
noncomputable def nb078AlphaDummy041 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy032)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy033)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_042`. -/
@[expose]
noncomputable def nb078AlphaDummy042 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy035 f)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy036 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_043`. -/
@[expose]
noncomputable def nb078AlphaDummy043 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy032))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_044`. -/
@[expose]
noncomputable def nb078AlphaDummy044 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy035 f))).fv ∪
      ((Class.cv (nb078AlphaDummy035 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_045`. -/
@[expose]
noncomputable def nb078AlphaDummy045 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy033))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_046`. -/
@[expose]
noncomputable def nb078AlphaDummy046 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy036 f))).fv ∪
      ((Class.cv (nb078AlphaDummy036 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_047`. -/
@[expose]
noncomputable def nb078AlphaDummy047 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy017)
          (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
            (Wff.classEq (Class.cv (nb078AlphaDummy017))
              (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy017)
          (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
            (Wff.classEq (Class.cv (nb078AlphaDummy017))
              (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_048`. -/
@[expose]
noncomputable def nb078AlphaDummy048 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy019 f)
          (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy019 f)
          (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_049`. -/
@[expose]
noncomputable def nb078AlphaDummy049 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy018))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_050`. -/
@[expose]
noncomputable def nb078AlphaDummy050 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy020 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_051`. -/
@[expose]
noncomputable def nb078AlphaDummy051 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy018)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy018)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_052`. -/
@[expose]
noncomputable def nb078AlphaDummy052 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy020 f)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy020 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_053`. -/
@[expose]
noncomputable def nb078AlphaDummy053 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_054`. -/
@[expose]
noncomputable def nb078AlphaDummy054 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_055`. -/
@[expose]
noncomputable def nb078AlphaDummy055 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy012 f))).fv ∪
      ((Class.cv (nb078AlphaDummy014 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_056`. -/
@[expose]
noncomputable def nb078AlphaDummy056 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy012 f))).fv ∪
      ((Class.cv (nb078AlphaDummy014 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_057`. -/
@[expose]
noncomputable def nb078AlphaDummy057 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCphi (Class.cv (nb078AlphaDummy054)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_058`. -/
@[expose]
noncomputable def nb078AlphaDummy058 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCphi (Class.cv (nb078AlphaDummy056 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_059`. -/
@[expose]
noncomputable def nb078AlphaDummy059 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy053)
          (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
            (Wff.classEq (Class.cv (nb078AlphaDummy053))
              (synCphi (Class.cv (nb078AlphaDummy054))))))).fv ∪
      ((Class.cab (nb078AlphaDummy053)
          (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
            (Wff.classEq (Class.cv (nb078AlphaDummy053))
              (synCphi (Class.cv (nb078AlphaDummy054))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_060`. -/
@[expose]
noncomputable def nb078AlphaDummy060 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy055 f)
          (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
              (synCphi (Class.cv (nb078AlphaDummy056 f))))))).fv ∪
      ((Class.cab (nb078AlphaDummy055 f)
          (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
              (synCphi (Class.cv (nb078AlphaDummy056 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_061`. -/
@[expose]
noncomputable def nb078AlphaDummy061 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy054))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_062`. -/
@[expose]
noncomputable def nb078AlphaDummy062 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy054))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_063`. -/
@[expose]
noncomputable def nb078AlphaDummy063 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy056 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_064`. -/
@[expose]
noncomputable def nb078AlphaDummy064 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy056 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_065`. -/
@[expose]
noncomputable def nb078AlphaDummy065 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy061)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy061)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy061))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_066`. -/
@[expose]
noncomputable def nb078AlphaDummy066 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy063 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy063 f)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy063 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_067`. -/
@[expose]
noncomputable def nb078AlphaDummy067 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_068`. -/
@[expose]
noncomputable def nb078AlphaDummy068 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_069`. -/
@[expose]
noncomputable def nb078AlphaDummy069 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_070`. -/
@[expose]
noncomputable def nb078AlphaDummy070 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_071`. -/
@[expose]
noncomputable def nb078AlphaDummy071 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_072`. -/
@[expose]
noncomputable def nb078AlphaDummy072 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_073`. -/
@[expose]
noncomputable def nb078AlphaDummy073 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy068))
          (Class.cv (nb078AlphaDummy069)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy068)) (Class.cv (nb078AlphaDummy069)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_074`. -/
@[expose]
noncomputable def nb078AlphaDummy074 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy071 f))
          (Class.cv (nb078AlphaDummy072 f)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy071 f)) (Class.cv (nb078AlphaDummy072 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_075`. -/
@[expose]
noncomputable def nb078AlphaDummy075 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_076`. -/
@[expose]
noncomputable def nb078AlphaDummy076 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy071 f))).fv ∪
      ((Class.cv (nb078AlphaDummy072 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_077`. -/
@[expose]
noncomputable def nb078AlphaDummy077 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy068)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy069)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_078`. -/
@[expose]
noncomputable def nb078AlphaDummy078 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy071 f)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy072 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_079`. -/
@[expose]
noncomputable def nb078AlphaDummy079 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy068))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_080`. -/
@[expose]
noncomputable def nb078AlphaDummy080 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy071 f))).fv ∪
      ((Class.cv (nb078AlphaDummy071 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_081`. -/
@[expose]
noncomputable def nb078AlphaDummy081 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy069))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_082`. -/
@[expose]
noncomputable def nb078AlphaDummy082 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy072 f))).fv ∪
      ((Class.cv (nb078AlphaDummy072 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_083`. -/
@[expose]
noncomputable def nb078AlphaDummy083 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy053)
          (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
            (Wff.classEq (Class.cv (nb078AlphaDummy053))
              (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy053)
          (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
            (Wff.classEq (Class.cv (nb078AlphaDummy053))
              (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_084`. -/
@[expose]
noncomputable def nb078AlphaDummy084 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy055 f)
          (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy055 f)
          (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_085`. -/
@[expose]
noncomputable def nb078AlphaDummy085 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy054))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_086`. -/
@[expose]
noncomputable def nb078AlphaDummy086 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy056 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_087`. -/
@[expose]
noncomputable def nb078AlphaDummy087 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy054)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy054)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_088`. -/
@[expose]
noncomputable def nb078AlphaDummy088 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy056 f)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy056 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_089`. -/
@[expose]
noncomputable def nb078AlphaDummy089 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_090`. -/
@[expose]
noncomputable def nb078AlphaDummy090 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_091`. -/
@[expose]
noncomputable def nb078AlphaDummy091 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_092`. -/
@[expose]
noncomputable def nb078AlphaDummy092 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_093`. -/
@[expose]
noncomputable def nb078AlphaDummy093 : Var :=
  (freshVar
    (({(nb078AlphaDummy089)} : Finset Var) ∪ ({(nb078AlphaDummy090)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy090)) (Class.cv (nb078AlphaDummy000))
          (Class.cv (nb078AlphaDummy089)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_094`. -/
@[expose]
noncomputable def nb078AlphaDummy094 (f : Var) : Var :=
  (freshVar (({(nb078AlphaDummy091 f)} : Finset Var) ∪
        ({(nb078AlphaDummy092 f)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy092 f)) (Class.cv f)
          (Class.cv (nb078AlphaDummy091 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_095`. -/
@[expose]
noncomputable def nb078AlphaDummy095 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_096`. -/
@[expose]
noncomputable def nb078AlphaDummy096 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_097`. -/
@[expose]
noncomputable def nb078AlphaDummy097 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy091 f))).fv ∪
      ((Class.cv (nb078AlphaDummy092 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_098`. -/
@[expose]
noncomputable def nb078AlphaDummy098 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy091 f))).fv ∪
      ((Class.cv (nb078AlphaDummy092 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_099`. -/
@[expose]
noncomputable def nb078AlphaDummy099 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_100`. -/
@[expose]
noncomputable def nb078AlphaDummy100 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_101`. -/
@[expose]
noncomputable def nb078AlphaDummy101 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy095)
          (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
            (Wff.classEq (Class.cv (nb078AlphaDummy095))
              (synCphi (Class.cv (nb078AlphaDummy096))))))).fv ∪
      ((Class.cab (nb078AlphaDummy095)
          (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
            (Wff.classEq (Class.cv (nb078AlphaDummy095))
              (synCphi (Class.cv (nb078AlphaDummy096))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_102`. -/
@[expose]
noncomputable def nb078AlphaDummy102 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy097 f)
          (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
              (synCphi (Class.cv (nb078AlphaDummy098 f))))))).fv ∪
      ((Class.cab (nb078AlphaDummy097 f)
          (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
              (synCphi (Class.cv (nb078AlphaDummy098 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_103`. -/
@[expose]
noncomputable def nb078AlphaDummy103 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy096))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_104`. -/
@[expose]
noncomputable def nb078AlphaDummy104 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy096))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_105`. -/
@[expose]
noncomputable def nb078AlphaDummy105 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy098 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_106`. -/
@[expose]
noncomputable def nb078AlphaDummy106 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy098 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_107`. -/
@[expose]
noncomputable def nb078AlphaDummy107 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy103)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy103)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy103))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_108`. -/
@[expose]
noncomputable def nb078AlphaDummy108 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy105 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy105 f)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy105 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_109`. -/
@[expose]
noncomputable def nb078AlphaDummy109 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_110`. -/
@[expose]
noncomputable def nb078AlphaDummy110 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_111`. -/
@[expose]
noncomputable def nb078AlphaDummy111 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_112`. -/
@[expose]
noncomputable def nb078AlphaDummy112 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_113`. -/
@[expose]
noncomputable def nb078AlphaDummy113 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_114`. -/
@[expose]
noncomputable def nb078AlphaDummy114 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_115`. -/
@[expose]
noncomputable def nb078AlphaDummy115 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy110))
          (Class.cv (nb078AlphaDummy111)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy110)) (Class.cv (nb078AlphaDummy111)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_116`. -/
@[expose]
noncomputable def nb078AlphaDummy116 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy113 f))
          (Class.cv (nb078AlphaDummy114 f)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy113 f)) (Class.cv (nb078AlphaDummy114 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_117`. -/
@[expose]
noncomputable def nb078AlphaDummy117 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_118`. -/
@[expose]
noncomputable def nb078AlphaDummy118 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy113 f))).fv ∪
      ((Class.cv (nb078AlphaDummy114 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_119`. -/
@[expose]
noncomputable def nb078AlphaDummy119 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy110)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy111)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_120`. -/
@[expose]
noncomputable def nb078AlphaDummy120 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy113 f)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy114 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_121`. -/
@[expose]
noncomputable def nb078AlphaDummy121 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy110))).fv ∪ ((Class.cv (nb078AlphaDummy110))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_122`. -/
@[expose]
noncomputable def nb078AlphaDummy122 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy113 f))).fv ∪
      ((Class.cv (nb078AlphaDummy113 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_123`. -/
@[expose]
noncomputable def nb078AlphaDummy123 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy111))).fv ∪ ((Class.cv (nb078AlphaDummy111))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_124`. -/
@[expose]
noncomputable def nb078AlphaDummy124 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy114 f))).fv ∪
      ((Class.cv (nb078AlphaDummy114 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_125`. -/
@[expose]
noncomputable def nb078AlphaDummy125 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy095)
          (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
            (Wff.classEq (Class.cv (nb078AlphaDummy095))
              (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy095)
          (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
            (Wff.classEq (Class.cv (nb078AlphaDummy095))
              (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_126`. -/
@[expose]
noncomputable def nb078AlphaDummy126 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy097 f)
          (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy097 f)
          (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_127`. -/
@[expose]
noncomputable def nb078AlphaDummy127 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy096))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_128`. -/
@[expose]
noncomputable def nb078AlphaDummy128 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy098 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_129`. -/
@[expose]
noncomputable def nb078AlphaDummy129 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy096)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy096)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_130`. -/
@[expose]
noncomputable def nb078AlphaDummy130 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy098 f)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy098 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_131`. -/
@[expose]
noncomputable def nb078AlphaDummy131 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_132`. -/
@[expose]
noncomputable def nb078AlphaDummy132 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_133`. -/
@[expose]
noncomputable def nb078AlphaDummy133 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy092 f))).fv ∪
      ((Class.cv (nb078AlphaDummy091 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_134`. -/
@[expose]
noncomputable def nb078AlphaDummy134 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy092 f))).fv ∪
      ((Class.cv (nb078AlphaDummy091 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_135`. -/
@[expose]
noncomputable def nb078AlphaDummy135 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCphi (Class.cv (nb078AlphaDummy132)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_136`. -/
@[expose]
noncomputable def nb078AlphaDummy136 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCphi (Class.cv (nb078AlphaDummy134 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_137`. -/
@[expose]
noncomputable def nb078AlphaDummy137 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy131)
          (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
            (Wff.classEq (Class.cv (nb078AlphaDummy131))
              (synCphi (Class.cv (nb078AlphaDummy132))))))).fv ∪
      ((Class.cab (nb078AlphaDummy131)
          (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
            (Wff.classEq (Class.cv (nb078AlphaDummy131))
              (synCphi (Class.cv (nb078AlphaDummy132))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_138`. -/
@[expose]
noncomputable def nb078AlphaDummy138 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy133 f)
          (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
              (synCphi (Class.cv (nb078AlphaDummy134 f))))))).fv ∪
      ((Class.cab (nb078AlphaDummy133 f)
          (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
              (synCphi (Class.cv (nb078AlphaDummy134 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_139`. -/
@[expose]
noncomputable def nb078AlphaDummy139 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy132))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_140`. -/
@[expose]
noncomputable def nb078AlphaDummy140 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy132))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_141`. -/
@[expose]
noncomputable def nb078AlphaDummy141 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy134 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_142`. -/
@[expose]
noncomputable def nb078AlphaDummy142 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy134 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_143`. -/
@[expose]
noncomputable def nb078AlphaDummy143 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy139)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy139)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy139))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_144`. -/
@[expose]
noncomputable def nb078AlphaDummy144 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy141 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy141 f)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy141 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_145`. -/
@[expose]
noncomputable def nb078AlphaDummy145 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_146`. -/
@[expose]
noncomputable def nb078AlphaDummy146 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_147`. -/
@[expose]
noncomputable def nb078AlphaDummy147 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_148`. -/
@[expose]
noncomputable def nb078AlphaDummy148 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_149`. -/
@[expose]
noncomputable def nb078AlphaDummy149 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_150`. -/
@[expose]
noncomputable def nb078AlphaDummy150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_151`. -/
@[expose]
noncomputable def nb078AlphaDummy151 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy146))
          (Class.cv (nb078AlphaDummy147)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy146)) (Class.cv (nb078AlphaDummy147)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_152`. -/
@[expose]
noncomputable def nb078AlphaDummy152 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy149 f))
          (Class.cv (nb078AlphaDummy150 f)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy149 f)) (Class.cv (nb078AlphaDummy150 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_153`. -/
@[expose]
noncomputable def nb078AlphaDummy153 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_154`. -/
@[expose]
noncomputable def nb078AlphaDummy154 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy149 f))).fv ∪
      ((Class.cv (nb078AlphaDummy150 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_155`. -/
@[expose]
noncomputable def nb078AlphaDummy155 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy146)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy147)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_156`. -/
@[expose]
noncomputable def nb078AlphaDummy156 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy149 f)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy150 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_157`. -/
@[expose]
noncomputable def nb078AlphaDummy157 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy146))).fv ∪ ((Class.cv (nb078AlphaDummy146))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_158`. -/
@[expose]
noncomputable def nb078AlphaDummy158 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy149 f))).fv ∪
      ((Class.cv (nb078AlphaDummy149 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_159`. -/
@[expose]
noncomputable def nb078AlphaDummy159 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy147))).fv ∪ ((Class.cv (nb078AlphaDummy147))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_160`. -/
@[expose]
noncomputable def nb078AlphaDummy160 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy150 f))).fv ∪
      ((Class.cv (nb078AlphaDummy150 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_161`. -/
@[expose]
noncomputable def nb078AlphaDummy161 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy131)
          (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
            (Wff.classEq (Class.cv (nb078AlphaDummy131))
              (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy131)
          (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
            (Wff.classEq (Class.cv (nb078AlphaDummy131))
              (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_162`. -/
@[expose]
noncomputable def nb078AlphaDummy162 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy133 f)
          (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy133 f)
          (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_163`. -/
@[expose]
noncomputable def nb078AlphaDummy163 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy132))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_164`. -/
@[expose]
noncomputable def nb078AlphaDummy164 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy134 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_165`. -/
@[expose]
noncomputable def nb078AlphaDummy165 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy132)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy132)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_166`. -/
@[expose]
noncomputable def nb078AlphaDummy166 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy134 f)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy134 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_167`. -/
@[expose]
noncomputable def nb078AlphaDummy167 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_168`. -/
@[expose]
noncomputable def nb078AlphaDummy168 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_169`. -/
@[expose]
noncomputable def nb078AlphaDummy169 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy014 f))).fv ∪
      ((Class.cv (nb078AlphaDummy013 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_170`. -/
@[expose]
noncomputable def nb078AlphaDummy170 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy014 f))).fv ∪
      ((Class.cv (nb078AlphaDummy013 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_171`. -/
@[expose]
noncomputable def nb078AlphaDummy171 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCphi (Class.cv (nb078AlphaDummy168)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_172`. -/
@[expose]
noncomputable def nb078AlphaDummy172 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCphi (Class.cv (nb078AlphaDummy170 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_173`. -/
@[expose]
noncomputable def nb078AlphaDummy173 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy167)
          (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
            (Wff.classEq (Class.cv (nb078AlphaDummy167))
              (synCphi (Class.cv (nb078AlphaDummy168))))))).fv ∪
      ((Class.cab (nb078AlphaDummy167)
          (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
            (Wff.classEq (Class.cv (nb078AlphaDummy167))
              (synCphi (Class.cv (nb078AlphaDummy168))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_174`. -/
@[expose]
noncomputable def nb078AlphaDummy174 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy169 f)
          (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
              (synCphi (Class.cv (nb078AlphaDummy170 f))))))).fv ∪
      ((Class.cab (nb078AlphaDummy169 f)
          (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
              (synCphi (Class.cv (nb078AlphaDummy170 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_175`. -/
@[expose]
noncomputable def nb078AlphaDummy175 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy168))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_176`. -/
@[expose]
noncomputable def nb078AlphaDummy176 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy168))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_177`. -/
@[expose]
noncomputable def nb078AlphaDummy177 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy170 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_178`. -/
@[expose]
noncomputable def nb078AlphaDummy178 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy170 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_179`. -/
@[expose]
noncomputable def nb078AlphaDummy179 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy175)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy175)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy175))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_180`. -/
@[expose]
noncomputable def nb078AlphaDummy180 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy177 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy177 f)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy177 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_181`. -/
@[expose]
noncomputable def nb078AlphaDummy181 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_182`. -/
@[expose]
noncomputable def nb078AlphaDummy182 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_183`. -/
@[expose]
noncomputable def nb078AlphaDummy183 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_184`. -/
@[expose]
noncomputable def nb078AlphaDummy184 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_185`. -/
@[expose]
noncomputable def nb078AlphaDummy185 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_186`. -/
@[expose]
noncomputable def nb078AlphaDummy186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_187`. -/
@[expose]
noncomputable def nb078AlphaDummy187 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy182))
          (Class.cv (nb078AlphaDummy183)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy182)) (Class.cv (nb078AlphaDummy183)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_188`. -/
@[expose]
noncomputable def nb078AlphaDummy188 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy185 f))
          (Class.cv (nb078AlphaDummy186 f)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy185 f)) (Class.cv (nb078AlphaDummy186 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_189`. -/
@[expose]
noncomputable def nb078AlphaDummy189 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_190`. -/
@[expose]
noncomputable def nb078AlphaDummy190 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy185 f))).fv ∪
      ((Class.cv (nb078AlphaDummy186 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_191`. -/
@[expose]
noncomputable def nb078AlphaDummy191 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy182)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy183)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_192`. -/
@[expose]
noncomputable def nb078AlphaDummy192 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy185 f)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy186 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_193`. -/
@[expose]
noncomputable def nb078AlphaDummy193 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy182))).fv ∪ ((Class.cv (nb078AlphaDummy182))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_194`. -/
@[expose]
noncomputable def nb078AlphaDummy194 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy185 f))).fv ∪
      ((Class.cv (nb078AlphaDummy185 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_195`. -/
@[expose]
noncomputable def nb078AlphaDummy195 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy183))).fv ∪ ((Class.cv (nb078AlphaDummy183))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_196`. -/
@[expose]
noncomputable def nb078AlphaDummy196 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy186 f))).fv ∪
      ((Class.cv (nb078AlphaDummy186 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_197`. -/
@[expose]
noncomputable def nb078AlphaDummy197 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy167)
          (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
            (Wff.classEq (Class.cv (nb078AlphaDummy167))
              (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy167)
          (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
            (Wff.classEq (Class.cv (nb078AlphaDummy167))
              (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_198`. -/
@[expose]
noncomputable def nb078AlphaDummy198 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy169 f)
          (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy169 f)
          (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_199`. -/
@[expose]
noncomputable def nb078AlphaDummy199 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy168))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_200`. -/
@[expose]
noncomputable def nb078AlphaDummy200 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy170 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_201`. -/
@[expose]
noncomputable def nb078AlphaDummy201 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy168)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy168)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_202`. -/
@[expose]
noncomputable def nb078AlphaDummy202 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy170 f)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy170 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_203`. -/
@[expose]
noncomputable def nb078AlphaDummy203 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_204`. -/
@[expose]
noncomputable def nb078AlphaDummy204 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_205`. -/
@[expose]
noncomputable def nb078AlphaDummy205 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_206`. -/
@[expose]
noncomputable def nb078AlphaDummy206 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_207`. -/
@[expose]
noncomputable def nb078AlphaDummy207 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_208`. -/
@[expose]
noncomputable def nb078AlphaDummy208 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy204))).fv ∪ ((Class.cv (nb078AlphaDummy203))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_209`. -/
@[expose]
noncomputable def nb078AlphaDummy209 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy206 f))).fv ∪
      ((Class.cv (nb078AlphaDummy205 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_210`. -/
@[expose]
noncomputable def nb078AlphaDummy210 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy206 f))).fv ∪
      ((Class.cv (nb078AlphaDummy205 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_211`. -/
@[expose]
noncomputable def nb078AlphaDummy211 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCphi (Class.cv (nb078AlphaDummy208)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_212`. -/
@[expose]
noncomputable def nb078AlphaDummy212 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCphi (Class.cv (nb078AlphaDummy210 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_213`. -/
@[expose]
noncomputable def nb078AlphaDummy213 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy207)
          (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
            (Wff.classEq (Class.cv (nb078AlphaDummy207))
              (synCphi (Class.cv (nb078AlphaDummy208))))))).fv ∪
      ((Class.cab (nb078AlphaDummy207)
          (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
            (Wff.classEq (Class.cv (nb078AlphaDummy207))
              (synCphi (Class.cv (nb078AlphaDummy208))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_214`. -/
@[expose]
noncomputable def nb078AlphaDummy214 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy209 f)
          (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
              (synCphi (Class.cv (nb078AlphaDummy210 f))))))).fv ∪
      ((Class.cab (nb078AlphaDummy209 f)
          (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
              (synCphi (Class.cv (nb078AlphaDummy210 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_215`. -/
@[expose]
noncomputable def nb078AlphaDummy215 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy208))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_216`. -/
@[expose]
noncomputable def nb078AlphaDummy216 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy208))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_217`. -/
@[expose]
noncomputable def nb078AlphaDummy217 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy210 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_218`. -/
@[expose]
noncomputable def nb078AlphaDummy218 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy210 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_219`. -/
@[expose]
noncomputable def nb078AlphaDummy219 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy215)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy215)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy215))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_220`. -/
@[expose]
noncomputable def nb078AlphaDummy220 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy217 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy217 f)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy217 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_221`. -/
@[expose]
noncomputable def nb078AlphaDummy221 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_222`. -/
@[expose]
noncomputable def nb078AlphaDummy222 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_223`. -/
@[expose]
noncomputable def nb078AlphaDummy223 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_224`. -/
@[expose]
noncomputable def nb078AlphaDummy224 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_225`. -/
@[expose]
noncomputable def nb078AlphaDummy225 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_226`. -/
@[expose]
noncomputable def nb078AlphaDummy226 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_227`. -/
@[expose]
noncomputable def nb078AlphaDummy227 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy222))
          (Class.cv (nb078AlphaDummy223)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy222)) (Class.cv (nb078AlphaDummy223)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_228`. -/
@[expose]
noncomputable def nb078AlphaDummy228 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy225 f))
          (Class.cv (nb078AlphaDummy226 f)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy225 f)) (Class.cv (nb078AlphaDummy226 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_229`. -/
@[expose]
noncomputable def nb078AlphaDummy229 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_230`. -/
@[expose]
noncomputable def nb078AlphaDummy230 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy225 f))).fv ∪
      ((Class.cv (nb078AlphaDummy226 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_231`. -/
@[expose]
noncomputable def nb078AlphaDummy231 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy222)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy223)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_232`. -/
@[expose]
noncomputable def nb078AlphaDummy232 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy225 f)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy226 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_233`. -/
@[expose]
noncomputable def nb078AlphaDummy233 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy222))).fv ∪ ((Class.cv (nb078AlphaDummy222))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_234`. -/
@[expose]
noncomputable def nb078AlphaDummy234 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy225 f))).fv ∪
      ((Class.cv (nb078AlphaDummy225 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_235`. -/
@[expose]
noncomputable def nb078AlphaDummy235 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy223))).fv ∪ ((Class.cv (nb078AlphaDummy223))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_236`. -/
@[expose]
noncomputable def nb078AlphaDummy236 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy226 f))).fv ∪
      ((Class.cv (nb078AlphaDummy226 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_237`. -/
@[expose]
noncomputable def nb078AlphaDummy237 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy207)
          (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
            (Wff.classEq (Class.cv (nb078AlphaDummy207))
              (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy207)
          (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
            (Wff.classEq (Class.cv (nb078AlphaDummy207))
              (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_238`. -/
@[expose]
noncomputable def nb078AlphaDummy238 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy209 f)
          (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy209 f)
          (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_239`. -/
@[expose]
noncomputable def nb078AlphaDummy239 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy208))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_240`. -/
@[expose]
noncomputable def nb078AlphaDummy240 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy210 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_241`. -/
@[expose]
noncomputable def nb078AlphaDummy241 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy208)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy208)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_242`. -/
@[expose]
noncomputable def nb078AlphaDummy242 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy210 f)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy210 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_243`. -/
@[expose]
noncomputable def nb078AlphaDummy243 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_244`. -/
@[expose]
noncomputable def nb078AlphaDummy244 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_245`. -/
@[expose]
noncomputable def nb078AlphaDummy245 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_246`. -/
@[expose]
noncomputable def nb078AlphaDummy246 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_247`. -/
@[expose]
noncomputable def nb078AlphaDummy247 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_248`. -/
@[expose]
noncomputable def nb078AlphaDummy248 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy244))).fv ∪ ((Class.cv (nb078AlphaDummy243))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_249`. -/
@[expose]
noncomputable def nb078AlphaDummy249 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy246 f))).fv ∪
      ((Class.cv (nb078AlphaDummy245 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_250`. -/
@[expose]
noncomputable def nb078AlphaDummy250 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy246 f))).fv ∪
      ((Class.cv (nb078AlphaDummy245 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_251`. -/
@[expose]
noncomputable def nb078AlphaDummy251 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCphi (Class.cv (nb078AlphaDummy248)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_252`. -/
@[expose]
noncomputable def nb078AlphaDummy252 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCphi (Class.cv (nb078AlphaDummy250 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_253`. -/
@[expose]
noncomputable def nb078AlphaDummy253 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy247)
          (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
            (Wff.classEq (Class.cv (nb078AlphaDummy247))
              (synCphi (Class.cv (nb078AlphaDummy248))))))).fv ∪
      ((Class.cab (nb078AlphaDummy247)
          (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
            (Wff.classEq (Class.cv (nb078AlphaDummy247))
              (synCphi (Class.cv (nb078AlphaDummy248))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_254`. -/
@[expose]
noncomputable def nb078AlphaDummy254 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy249 f)
          (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
              (synCphi (Class.cv (nb078AlphaDummy250 f))))))).fv ∪
      ((Class.cab (nb078AlphaDummy249 f)
          (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
              (synCphi (Class.cv (nb078AlphaDummy250 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_255`. -/
@[expose]
noncomputable def nb078AlphaDummy255 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy248))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_256`. -/
@[expose]
noncomputable def nb078AlphaDummy256 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy248))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_257`. -/
@[expose]
noncomputable def nb078AlphaDummy257 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy250 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_258`. -/
@[expose]
noncomputable def nb078AlphaDummy258 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy250 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_259`. -/
@[expose]
noncomputable def nb078AlphaDummy259 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy255)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy255)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy255))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_260`. -/
@[expose]
noncomputable def nb078AlphaDummy260 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy257 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy257 f)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy257 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_261`. -/
@[expose]
noncomputable def nb078AlphaDummy261 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_262`. -/
@[expose]
noncomputable def nb078AlphaDummy262 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_263`. -/
@[expose]
noncomputable def nb078AlphaDummy263 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_264`. -/
@[expose]
noncomputable def nb078AlphaDummy264 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_265`. -/
@[expose]
noncomputable def nb078AlphaDummy265 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_266`. -/
@[expose]
noncomputable def nb078AlphaDummy266 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_267`. -/
@[expose]
noncomputable def nb078AlphaDummy267 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy262))
          (Class.cv (nb078AlphaDummy263)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy262)) (Class.cv (nb078AlphaDummy263)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_268`. -/
@[expose]
noncomputable def nb078AlphaDummy268 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy265 f))
          (Class.cv (nb078AlphaDummy266 f)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy265 f)) (Class.cv (nb078AlphaDummy266 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_269`. -/
@[expose]
noncomputable def nb078AlphaDummy269 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_270`. -/
@[expose]
noncomputable def nb078AlphaDummy270 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy265 f))).fv ∪
      ((Class.cv (nb078AlphaDummy266 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_271`. -/
@[expose]
noncomputable def nb078AlphaDummy271 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy262)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy263)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_272`. -/
@[expose]
noncomputable def nb078AlphaDummy272 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy265 f)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy266 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_273`. -/
@[expose]
noncomputable def nb078AlphaDummy273 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy262))).fv ∪ ((Class.cv (nb078AlphaDummy262))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_274`. -/
@[expose]
noncomputable def nb078AlphaDummy274 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy265 f))).fv ∪
      ((Class.cv (nb078AlphaDummy265 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_275`. -/
@[expose]
noncomputable def nb078AlphaDummy275 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy263))).fv ∪ ((Class.cv (nb078AlphaDummy263))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_276`. -/
@[expose]
noncomputable def nb078AlphaDummy276 (f : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy266 f))).fv ∪
      ((Class.cv (nb078AlphaDummy266 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_277`. -/
@[expose]
noncomputable def nb078AlphaDummy277 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy247)
          (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
            (Wff.classEq (Class.cv (nb078AlphaDummy247))
              (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy247)
          (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
            (Wff.classEq (Class.cv (nb078AlphaDummy247))
              (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_278`. -/
@[expose]
noncomputable def nb078AlphaDummy278 (f : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy249 f)
          (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy249 f)
          (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
            (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
              (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_279`. -/
@[expose]
noncomputable def nb078AlphaDummy279 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy248))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_280`. -/
@[expose]
noncomputable def nb078AlphaDummy280 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy250 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_281`. -/
@[expose]
noncomputable def nb078AlphaDummy281 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy248)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy248)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_282`. -/
@[expose]
noncomputable def nb078AlphaDummy282 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy250 f)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy250 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_283`. -/
@[expose]
noncomputable def nb078AlphaDummy283 : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb078AlphaDummy001))
            (synCcnv (Class.cv (nb078AlphaDummy001)))) (synCid))).fv ∪ ((synCnin
          (synCcom (Class.cv (nb078AlphaDummy001))
            (synCcnv (Class.cv (nb078AlphaDummy001)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_284`. -/
@[expose]
noncomputable def nb078AlphaDummy284 (g : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv g) (synCcnv (Class.cv g))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv g) (synCcnv (Class.cv g))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_285`. -/
@[expose]
noncomputable def nb078AlphaDummy285 : Var :=
  (freshVar (((synCcom (Class.cv (nb078AlphaDummy001))
          (synCcnv (Class.cv (nb078AlphaDummy001))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_286`. -/
@[expose]
noncomputable def nb078AlphaDummy286 (g : Var) : Var :=
  (freshVar (((synCcom (Class.cv g) (synCcnv (Class.cv g)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_287`. -/
@[expose]
noncomputable def nb078AlphaDummy287 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy001))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_288`. -/
@[expose]
noncomputable def nb078AlphaDummy288 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy001))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_289`. -/
@[expose]
noncomputable def nb078AlphaDummy289 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy001))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_290`. -/
@[expose]
noncomputable def nb078AlphaDummy290 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_291`. -/
@[expose]
noncomputable def nb078AlphaDummy291 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_292`. -/
@[expose]
noncomputable def nb078AlphaDummy292 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_293`. -/
@[expose]
noncomputable def nb078AlphaDummy293 : Var :=
  (freshVar
    (({(nb078AlphaDummy287)} : Finset Var) ∪ ({(nb078AlphaDummy288)} : Finset Var) ∪
      ((synWex (nb078AlphaDummy289) (synWa (synWbr (Class.cv (nb078AlphaDummy287))
              (synCcnv (Class.cv (nb078AlphaDummy001))) (Class.cv (nb078AlphaDummy289)))
            (synWbr (Class.cv (nb078AlphaDummy289)) (Class.cv (nb078AlphaDummy001))
              (Class.cv (nb078AlphaDummy288)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_294`. -/
@[expose]
noncomputable def nb078AlphaDummy294 (g : Var) : Var :=
  (freshVar (({(nb078AlphaDummy290 g)} : Finset Var) ∪
        ({(nb078AlphaDummy291 g)} : Finset Var) ∪ ((synWex (nb078AlphaDummy292 g) (synWa
            (synWbr (Class.cv (nb078AlphaDummy290 g)) (synCcnv (Class.cv g))
              (Class.cv (nb078AlphaDummy292 g)))
            (synWbr (Class.cv (nb078AlphaDummy292 g)) (Class.cv g)
              (Class.cv (nb078AlphaDummy291 g)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_295`. -/
@[expose]
noncomputable def nb078AlphaDummy295 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_296`. -/
@[expose]
noncomputable def nb078AlphaDummy296 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_297`. -/
@[expose]
noncomputable def nb078AlphaDummy297 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy290 g))).fv ∪
      ((Class.cv (nb078AlphaDummy291 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_298`. -/
@[expose]
noncomputable def nb078AlphaDummy298 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy290 g))).fv ∪
      ((Class.cv (nb078AlphaDummy291 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_299`. -/
@[expose]
noncomputable def nb078AlphaDummy299 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCphi (Class.cv (nb078AlphaDummy296)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                  (synCsn (synC0c)))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_300`. -/
@[expose]
noncomputable def nb078AlphaDummy300 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCphi (Class.cv (nb078AlphaDummy298 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_301`. -/
@[expose]
noncomputable def nb078AlphaDummy301 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy295)
          (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
            (Wff.classEq (Class.cv (nb078AlphaDummy295))
              (synCphi (Class.cv (nb078AlphaDummy296))))))).fv ∪
      ((Class.cab (nb078AlphaDummy295)
          (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
            (Wff.classEq (Class.cv (nb078AlphaDummy295))
              (synCphi (Class.cv (nb078AlphaDummy296))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_302`. -/
@[expose]
noncomputable def nb078AlphaDummy302 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy297 g)
          (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
              (synCphi (Class.cv (nb078AlphaDummy298 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy297 g)
          (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
              (synCphi (Class.cv (nb078AlphaDummy298 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_303`. -/
@[expose]
noncomputable def nb078AlphaDummy303 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy296))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_304`. -/
@[expose]
noncomputable def nb078AlphaDummy304 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy296))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_305`. -/
@[expose]
noncomputable def nb078AlphaDummy305 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy298 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_306`. -/
@[expose]
noncomputable def nb078AlphaDummy306 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy298 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_307`. -/
@[expose]
noncomputable def nb078AlphaDummy307 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy303)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy303)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy303))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_308`. -/
@[expose]
noncomputable def nb078AlphaDummy308 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy305 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy305 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy305 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_309`. -/
@[expose]
noncomputable def nb078AlphaDummy309 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_310`. -/
@[expose]
noncomputable def nb078AlphaDummy310 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_311`. -/
@[expose]
noncomputable def nb078AlphaDummy311 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_312`. -/
@[expose]
noncomputable def nb078AlphaDummy312 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_313`. -/
@[expose]
noncomputable def nb078AlphaDummy313 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_314`. -/
@[expose]
noncomputable def nb078AlphaDummy314 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_315`. -/
@[expose]
noncomputable def nb078AlphaDummy315 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy310))
          (Class.cv (nb078AlphaDummy311)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy310)) (Class.cv (nb078AlphaDummy311)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_316`. -/
@[expose]
noncomputable def nb078AlphaDummy316 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy313 g))
          (Class.cv (nb078AlphaDummy314 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy313 g)) (Class.cv (nb078AlphaDummy314 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_317`. -/
@[expose]
noncomputable def nb078AlphaDummy317 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_318`. -/
@[expose]
noncomputable def nb078AlphaDummy318 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy313 g))).fv ∪
      ((Class.cv (nb078AlphaDummy314 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_319`. -/
@[expose]
noncomputable def nb078AlphaDummy319 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy310)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy311)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_320`. -/
@[expose]
noncomputable def nb078AlphaDummy320 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy313 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy314 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_321`. -/
@[expose]
noncomputable def nb078AlphaDummy321 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy310))).fv ∪ ((Class.cv (nb078AlphaDummy310))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_322`. -/
@[expose]
noncomputable def nb078AlphaDummy322 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy313 g))).fv ∪
      ((Class.cv (nb078AlphaDummy313 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_323`. -/
@[expose]
noncomputable def nb078AlphaDummy323 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy311))).fv ∪ ((Class.cv (nb078AlphaDummy311))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_324`. -/
@[expose]
noncomputable def nb078AlphaDummy324 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy314 g))).fv ∪
      ((Class.cv (nb078AlphaDummy314 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_325`. -/
@[expose]
noncomputable def nb078AlphaDummy325 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy295)
          (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
            (Wff.classEq (Class.cv (nb078AlphaDummy295))
              (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy295)
          (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
            (Wff.classEq (Class.cv (nb078AlphaDummy295))
              (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_326`. -/
@[expose]
noncomputable def nb078AlphaDummy326 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy297 g)
          (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy297 g)
          (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_327`. -/
@[expose]
noncomputable def nb078AlphaDummy327 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy296))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_328`. -/
@[expose]
noncomputable def nb078AlphaDummy328 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy298 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_329`. -/
@[expose]
noncomputable def nb078AlphaDummy329 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy296)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy296)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_330`. -/
@[expose]
noncomputable def nb078AlphaDummy330 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy298 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy298 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_331`. -/
@[expose]
noncomputable def nb078AlphaDummy331 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_332`. -/
@[expose]
noncomputable def nb078AlphaDummy332 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy287))).fv ∪ ((Class.cv (nb078AlphaDummy289))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_333`. -/
@[expose]
noncomputable def nb078AlphaDummy333 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy290 g))).fv ∪
      ((Class.cv (nb078AlphaDummy292 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_334`. -/
@[expose]
noncomputable def nb078AlphaDummy334 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy290 g))).fv ∪
      ((Class.cv (nb078AlphaDummy292 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_335`. -/
@[expose]
noncomputable def nb078AlphaDummy335 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCphi (Class.cv (nb078AlphaDummy332)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_336`. -/
@[expose]
noncomputable def nb078AlphaDummy336 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCphi (Class.cv (nb078AlphaDummy334 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_337`. -/
@[expose]
noncomputable def nb078AlphaDummy337 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy331)
          (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
            (Wff.classEq (Class.cv (nb078AlphaDummy331))
              (synCphi (Class.cv (nb078AlphaDummy332))))))).fv ∪
      ((Class.cab (nb078AlphaDummy331)
          (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
            (Wff.classEq (Class.cv (nb078AlphaDummy331))
              (synCphi (Class.cv (nb078AlphaDummy332))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_338`. -/
@[expose]
noncomputable def nb078AlphaDummy338 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy333 g)
          (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
              (synCphi (Class.cv (nb078AlphaDummy334 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy333 g)
          (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
              (synCphi (Class.cv (nb078AlphaDummy334 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_339`. -/
@[expose]
noncomputable def nb078AlphaDummy339 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy332))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_340`. -/
@[expose]
noncomputable def nb078AlphaDummy340 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy332))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_341`. -/
@[expose]
noncomputable def nb078AlphaDummy341 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy334 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_342`. -/
@[expose]
noncomputable def nb078AlphaDummy342 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy334 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_343`. -/
@[expose]
noncomputable def nb078AlphaDummy343 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy339)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy339)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy339))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_344`. -/
@[expose]
noncomputable def nb078AlphaDummy344 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy341 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy341 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy341 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_345`. -/
@[expose]
noncomputable def nb078AlphaDummy345 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_346`. -/
@[expose]
noncomputable def nb078AlphaDummy346 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_347`. -/
@[expose]
noncomputable def nb078AlphaDummy347 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_348`. -/
@[expose]
noncomputable def nb078AlphaDummy348 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_349`. -/
@[expose]
noncomputable def nb078AlphaDummy349 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_350`. -/
@[expose]
noncomputable def nb078AlphaDummy350 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_351`. -/
@[expose]
noncomputable def nb078AlphaDummy351 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy346))
          (Class.cv (nb078AlphaDummy347)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy346)) (Class.cv (nb078AlphaDummy347)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_352`. -/
@[expose]
noncomputable def nb078AlphaDummy352 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy349 g))
          (Class.cv (nb078AlphaDummy350 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy349 g)) (Class.cv (nb078AlphaDummy350 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_353`. -/
@[expose]
noncomputable def nb078AlphaDummy353 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_354`. -/
@[expose]
noncomputable def nb078AlphaDummy354 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy349 g))).fv ∪
      ((Class.cv (nb078AlphaDummy350 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_355`. -/
@[expose]
noncomputable def nb078AlphaDummy355 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy346)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy347)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_356`. -/
@[expose]
noncomputable def nb078AlphaDummy356 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy349 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy350 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_357`. -/
@[expose]
noncomputable def nb078AlphaDummy357 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy346))).fv ∪ ((Class.cv (nb078AlphaDummy346))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_358`. -/
@[expose]
noncomputable def nb078AlphaDummy358 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy349 g))).fv ∪
      ((Class.cv (nb078AlphaDummy349 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_359`. -/
@[expose]
noncomputable def nb078AlphaDummy359 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy347))).fv ∪ ((Class.cv (nb078AlphaDummy347))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_360`. -/
@[expose]
noncomputable def nb078AlphaDummy360 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy350 g))).fv ∪
      ((Class.cv (nb078AlphaDummy350 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_361`. -/
@[expose]
noncomputable def nb078AlphaDummy361 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy331)
          (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
            (Wff.classEq (Class.cv (nb078AlphaDummy331))
              (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy331)
          (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
            (Wff.classEq (Class.cv (nb078AlphaDummy331))
              (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_362`. -/
@[expose]
noncomputable def nb078AlphaDummy362 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy333 g)
          (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy333 g)
          (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_363`. -/
@[expose]
noncomputable def nb078AlphaDummy363 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy332))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_364`. -/
@[expose]
noncomputable def nb078AlphaDummy364 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy334 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_365`. -/
@[expose]
noncomputable def nb078AlphaDummy365 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy332)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy332)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_366`. -/
@[expose]
noncomputable def nb078AlphaDummy366 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy334 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy334 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_367`. -/
@[expose]
noncomputable def nb078AlphaDummy367 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_368`. -/
@[expose]
noncomputable def nb078AlphaDummy368 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_369`. -/
@[expose]
noncomputable def nb078AlphaDummy369 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_370`. -/
@[expose]
noncomputable def nb078AlphaDummy370 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_371`. -/
@[expose]
noncomputable def nb078AlphaDummy371 : Var :=
  (freshVar
    (({(nb078AlphaDummy367)} : Finset Var) ∪ ({(nb078AlphaDummy368)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy368)) (Class.cv (nb078AlphaDummy001))
          (Class.cv (nb078AlphaDummy367)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_372`. -/
@[expose]
noncomputable def nb078AlphaDummy372 (g : Var) : Var :=
  (freshVar (({(nb078AlphaDummy369 g)} : Finset Var) ∪
        ({(nb078AlphaDummy370 g)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy370 g)) (Class.cv g)
          (Class.cv (nb078AlphaDummy369 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_373`. -/
@[expose]
noncomputable def nb078AlphaDummy373 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_374`. -/
@[expose]
noncomputable def nb078AlphaDummy374 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy367))).fv ∪ ((Class.cv (nb078AlphaDummy368))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_375`. -/
@[expose]
noncomputable def nb078AlphaDummy375 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy369 g))).fv ∪
      ((Class.cv (nb078AlphaDummy370 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_376`. -/
@[expose]
noncomputable def nb078AlphaDummy376 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy369 g))).fv ∪
      ((Class.cv (nb078AlphaDummy370 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_377`. -/
@[expose]
noncomputable def nb078AlphaDummy377 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_378`. -/
@[expose]
noncomputable def nb078AlphaDummy378 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_379`. -/
@[expose]
noncomputable def nb078AlphaDummy379 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy373)
          (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
            (Wff.classEq (Class.cv (nb078AlphaDummy373))
              (synCphi (Class.cv (nb078AlphaDummy374))))))).fv ∪
      ((Class.cab (nb078AlphaDummy373)
          (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
            (Wff.classEq (Class.cv (nb078AlphaDummy373))
              (synCphi (Class.cv (nb078AlphaDummy374))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_380`. -/
@[expose]
noncomputable def nb078AlphaDummy380 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy375 g)
          (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
              (synCphi (Class.cv (nb078AlphaDummy376 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy375 g)
          (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
              (synCphi (Class.cv (nb078AlphaDummy376 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_381`. -/
@[expose]
noncomputable def nb078AlphaDummy381 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy374))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_382`. -/
@[expose]
noncomputable def nb078AlphaDummy382 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy374))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_383`. -/
@[expose]
noncomputable def nb078AlphaDummy383 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy376 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_384`. -/
@[expose]
noncomputable def nb078AlphaDummy384 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy376 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_385`. -/
@[expose]
noncomputable def nb078AlphaDummy385 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy381)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy381)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy381))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_386`. -/
@[expose]
noncomputable def nb078AlphaDummy386 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy383 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy383 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy383 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_387`. -/
@[expose]
noncomputable def nb078AlphaDummy387 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_388`. -/
@[expose]
noncomputable def nb078AlphaDummy388 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_389`. -/
@[expose]
noncomputable def nb078AlphaDummy389 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_390`. -/
@[expose]
noncomputable def nb078AlphaDummy390 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_391`. -/
@[expose]
noncomputable def nb078AlphaDummy391 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_392`. -/
@[expose]
noncomputable def nb078AlphaDummy392 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_393`. -/
@[expose]
noncomputable def nb078AlphaDummy393 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy388))
          (Class.cv (nb078AlphaDummy389)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy388)) (Class.cv (nb078AlphaDummy389)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_394`. -/
@[expose]
noncomputable def nb078AlphaDummy394 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy391 g))
          (Class.cv (nb078AlphaDummy392 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy391 g)) (Class.cv (nb078AlphaDummy392 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_395`. -/
@[expose]
noncomputable def nb078AlphaDummy395 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_396`. -/
@[expose]
noncomputable def nb078AlphaDummy396 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy391 g))).fv ∪
      ((Class.cv (nb078AlphaDummy392 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_397`. -/
@[expose]
noncomputable def nb078AlphaDummy397 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy388)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy389)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_398`. -/
@[expose]
noncomputable def nb078AlphaDummy398 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy391 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy392 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_399`. -/
@[expose]
noncomputable def nb078AlphaDummy399 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy388))).fv ∪ ((Class.cv (nb078AlphaDummy388))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_400`. -/
@[expose]
noncomputable def nb078AlphaDummy400 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy391 g))).fv ∪
      ((Class.cv (nb078AlphaDummy391 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_401`. -/
@[expose]
noncomputable def nb078AlphaDummy401 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy389))).fv ∪ ((Class.cv (nb078AlphaDummy389))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_402`. -/
@[expose]
noncomputable def nb078AlphaDummy402 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy392 g))).fv ∪
      ((Class.cv (nb078AlphaDummy392 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_403`. -/
@[expose]
noncomputable def nb078AlphaDummy403 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy373)
          (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
            (Wff.classEq (Class.cv (nb078AlphaDummy373))
              (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy373)
          (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
            (Wff.classEq (Class.cv (nb078AlphaDummy373))
              (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_404`. -/
@[expose]
noncomputable def nb078AlphaDummy404 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy375 g)
          (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy375 g)
          (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_405`. -/
@[expose]
noncomputable def nb078AlphaDummy405 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy374))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_406`. -/
@[expose]
noncomputable def nb078AlphaDummy406 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy376 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_407`. -/
@[expose]
noncomputable def nb078AlphaDummy407 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy374)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy374)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_408`. -/
@[expose]
noncomputable def nb078AlphaDummy408 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy376 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy376 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_409`. -/
@[expose]
noncomputable def nb078AlphaDummy409 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_410`. -/
@[expose]
noncomputable def nb078AlphaDummy410 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy368))).fv ∪ ((Class.cv (nb078AlphaDummy367))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_411`. -/
@[expose]
noncomputable def nb078AlphaDummy411 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy370 g))).fv ∪
      ((Class.cv (nb078AlphaDummy369 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_412`. -/
@[expose]
noncomputable def nb078AlphaDummy412 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy370 g))).fv ∪
      ((Class.cv (nb078AlphaDummy369 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_413`. -/
@[expose]
noncomputable def nb078AlphaDummy413 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_414`. -/
@[expose]
noncomputable def nb078AlphaDummy414 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_415`. -/
@[expose]
noncomputable def nb078AlphaDummy415 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy409)
          (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
            (Wff.classEq (Class.cv (nb078AlphaDummy409))
              (synCphi (Class.cv (nb078AlphaDummy410))))))).fv ∪
      ((Class.cab (nb078AlphaDummy409)
          (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
            (Wff.classEq (Class.cv (nb078AlphaDummy409))
              (synCphi (Class.cv (nb078AlphaDummy410))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_416`. -/
@[expose]
noncomputable def nb078AlphaDummy416 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy411 g)
          (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
              (synCphi (Class.cv (nb078AlphaDummy412 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy411 g)
          (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
              (synCphi (Class.cv (nb078AlphaDummy412 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_417`. -/
@[expose]
noncomputable def nb078AlphaDummy417 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy410))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_418`. -/
@[expose]
noncomputable def nb078AlphaDummy418 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy410))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_419`. -/
@[expose]
noncomputable def nb078AlphaDummy419 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy412 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_420`. -/
@[expose]
noncomputable def nb078AlphaDummy420 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy412 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_421`. -/
@[expose]
noncomputable def nb078AlphaDummy421 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy417)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy417)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy417))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_422`. -/
@[expose]
noncomputable def nb078AlphaDummy422 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy419 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy419 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy419 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_423`. -/
@[expose]
noncomputable def nb078AlphaDummy423 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_424`. -/
@[expose]
noncomputable def nb078AlphaDummy424 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_425`. -/
@[expose]
noncomputable def nb078AlphaDummy425 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_426`. -/
@[expose]
noncomputable def nb078AlphaDummy426 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_427`. -/
@[expose]
noncomputable def nb078AlphaDummy427 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_428`. -/
@[expose]
noncomputable def nb078AlphaDummy428 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_429`. -/
@[expose]
noncomputable def nb078AlphaDummy429 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy424))
          (Class.cv (nb078AlphaDummy425)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy424)) (Class.cv (nb078AlphaDummy425)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_430`. -/
@[expose]
noncomputable def nb078AlphaDummy430 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy427 g))
          (Class.cv (nb078AlphaDummy428 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy427 g)) (Class.cv (nb078AlphaDummy428 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_431`. -/
@[expose]
noncomputable def nb078AlphaDummy431 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_432`. -/
@[expose]
noncomputable def nb078AlphaDummy432 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy427 g))).fv ∪
      ((Class.cv (nb078AlphaDummy428 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_433`. -/
@[expose]
noncomputable def nb078AlphaDummy433 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy424)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy425)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_434`. -/
@[expose]
noncomputable def nb078AlphaDummy434 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy427 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy428 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_435`. -/
@[expose]
noncomputable def nb078AlphaDummy435 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy424))).fv ∪ ((Class.cv (nb078AlphaDummy424))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_436`. -/
@[expose]
noncomputable def nb078AlphaDummy436 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy427 g))).fv ∪
      ((Class.cv (nb078AlphaDummy427 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_437`. -/
@[expose]
noncomputable def nb078AlphaDummy437 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy425))).fv ∪ ((Class.cv (nb078AlphaDummy425))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_438`. -/
@[expose]
noncomputable def nb078AlphaDummy438 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy428 g))).fv ∪
      ((Class.cv (nb078AlphaDummy428 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_439`. -/
@[expose]
noncomputable def nb078AlphaDummy439 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy409)
          (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
            (Wff.classEq (Class.cv (nb078AlphaDummy409))
              (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy409)
          (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
            (Wff.classEq (Class.cv (nb078AlphaDummy409))
              (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_440`. -/
@[expose]
noncomputable def nb078AlphaDummy440 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy411 g)
          (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy411 g)
          (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_441`. -/
@[expose]
noncomputable def nb078AlphaDummy441 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy410))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_442`. -/
@[expose]
noncomputable def nb078AlphaDummy442 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy412 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_443`. -/
@[expose]
noncomputable def nb078AlphaDummy443 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy410)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy410)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_444`. -/
@[expose]
noncomputable def nb078AlphaDummy444 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy412 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy412 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_445`. -/
@[expose]
noncomputable def nb078AlphaDummy445 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_446`. -/
@[expose]
noncomputable def nb078AlphaDummy446 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy289))).fv ∪ ((Class.cv (nb078AlphaDummy288))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_447`. -/
@[expose]
noncomputable def nb078AlphaDummy447 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy292 g))).fv ∪
      ((Class.cv (nb078AlphaDummy291 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_448`. -/
@[expose]
noncomputable def nb078AlphaDummy448 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy292 g))).fv ∪
      ((Class.cv (nb078AlphaDummy291 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_449`. -/
@[expose]
noncomputable def nb078AlphaDummy449 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCphi (Class.cv (nb078AlphaDummy446)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                  (synCsn (synC0c)))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_450`. -/
@[expose]
noncomputable def nb078AlphaDummy450 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCphi (Class.cv (nb078AlphaDummy448 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_451`. -/
@[expose]
noncomputable def nb078AlphaDummy451 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy445)
          (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
            (Wff.classEq (Class.cv (nb078AlphaDummy445))
              (synCphi (Class.cv (nb078AlphaDummy446))))))).fv ∪
      ((Class.cab (nb078AlphaDummy445)
          (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
            (Wff.classEq (Class.cv (nb078AlphaDummy445))
              (synCphi (Class.cv (nb078AlphaDummy446))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_452`. -/
@[expose]
noncomputable def nb078AlphaDummy452 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy447 g)
          (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
              (synCphi (Class.cv (nb078AlphaDummy448 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy447 g)
          (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
              (synCphi (Class.cv (nb078AlphaDummy448 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_453`. -/
@[expose]
noncomputable def nb078AlphaDummy453 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy446))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_454`. -/
@[expose]
noncomputable def nb078AlphaDummy454 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy446))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_455`. -/
@[expose]
noncomputable def nb078AlphaDummy455 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy448 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_456`. -/
@[expose]
noncomputable def nb078AlphaDummy456 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy448 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_457`. -/
@[expose]
noncomputable def nb078AlphaDummy457 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy453)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy453)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy453))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_458`. -/
@[expose]
noncomputable def nb078AlphaDummy458 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy455 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy455 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy455 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_459`. -/
@[expose]
noncomputable def nb078AlphaDummy459 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_460`. -/
@[expose]
noncomputable def nb078AlphaDummy460 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_461`. -/
@[expose]
noncomputable def nb078AlphaDummy461 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_462`. -/
@[expose]
noncomputable def nb078AlphaDummy462 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_463`. -/
@[expose]
noncomputable def nb078AlphaDummy463 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_464`. -/
@[expose]
noncomputable def nb078AlphaDummy464 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_465`. -/
@[expose]
noncomputable def nb078AlphaDummy465 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy460))
          (Class.cv (nb078AlphaDummy461)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy460)) (Class.cv (nb078AlphaDummy461)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_466`. -/
@[expose]
noncomputable def nb078AlphaDummy466 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy463 g))
          (Class.cv (nb078AlphaDummy464 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy463 g)) (Class.cv (nb078AlphaDummy464 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_467`. -/
@[expose]
noncomputable def nb078AlphaDummy467 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_468`. -/
@[expose]
noncomputable def nb078AlphaDummy468 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy463 g))).fv ∪
      ((Class.cv (nb078AlphaDummy464 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_469`. -/
@[expose]
noncomputable def nb078AlphaDummy469 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy460)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy461)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_470`. -/
@[expose]
noncomputable def nb078AlphaDummy470 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy463 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy464 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_471`. -/
@[expose]
noncomputable def nb078AlphaDummy471 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy460))).fv ∪ ((Class.cv (nb078AlphaDummy460))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_472`. -/
@[expose]
noncomputable def nb078AlphaDummy472 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy463 g))).fv ∪
      ((Class.cv (nb078AlphaDummy463 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_473`. -/
@[expose]
noncomputable def nb078AlphaDummy473 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy461))).fv ∪ ((Class.cv (nb078AlphaDummy461))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_474`. -/
@[expose]
noncomputable def nb078AlphaDummy474 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy464 g))).fv ∪
      ((Class.cv (nb078AlphaDummy464 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_475`. -/
@[expose]
noncomputable def nb078AlphaDummy475 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy445)
          (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
            (Wff.classEq (Class.cv (nb078AlphaDummy445))
              (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy445)
          (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
            (Wff.classEq (Class.cv (nb078AlphaDummy445))
              (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_476`. -/
@[expose]
noncomputable def nb078AlphaDummy476 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy447 g)
          (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy447 g)
          (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_477`. -/
@[expose]
noncomputable def nb078AlphaDummy477 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy446))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_478`. -/
@[expose]
noncomputable def nb078AlphaDummy478 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy448 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_479`. -/
@[expose]
noncomputable def nb078AlphaDummy479 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy446)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy446)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_480`. -/
@[expose]
noncomputable def nb078AlphaDummy480 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy448 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy448 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_481`. -/
@[expose]
noncomputable def nb078AlphaDummy481 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_482`. -/
@[expose]
noncomputable def nb078AlphaDummy482 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_483`. -/
@[expose]
noncomputable def nb078AlphaDummy483 (g : Var) : Var :=
  (freshVar (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_484`. -/
@[expose]
noncomputable def nb078AlphaDummy484 (g : Var) : Var :=
  (freshVar (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_485`. -/
@[expose]
noncomputable def nb078AlphaDummy485 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_486`. -/
@[expose]
noncomputable def nb078AlphaDummy486 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy482))).fv ∪ ((Class.cv (nb078AlphaDummy481))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_487`. -/
@[expose]
noncomputable def nb078AlphaDummy487 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy484 g))).fv ∪
      ((Class.cv (nb078AlphaDummy483 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_488`. -/
@[expose]
noncomputable def nb078AlphaDummy488 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy484 g))).fv ∪
      ((Class.cv (nb078AlphaDummy483 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_489`. -/
@[expose]
noncomputable def nb078AlphaDummy489 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCphi (Class.cv (nb078AlphaDummy486)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_490`. -/
@[expose]
noncomputable def nb078AlphaDummy490 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCphi (Class.cv (nb078AlphaDummy488 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_491`. -/
@[expose]
noncomputable def nb078AlphaDummy491 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy485)
          (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
            (Wff.classEq (Class.cv (nb078AlphaDummy485))
              (synCphi (Class.cv (nb078AlphaDummy486))))))).fv ∪
      ((Class.cab (nb078AlphaDummy485)
          (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
            (Wff.classEq (Class.cv (nb078AlphaDummy485))
              (synCphi (Class.cv (nb078AlphaDummy486))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_492`. -/
@[expose]
noncomputable def nb078AlphaDummy492 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy487 g)
          (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
              (synCphi (Class.cv (nb078AlphaDummy488 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy487 g)
          (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
              (synCphi (Class.cv (nb078AlphaDummy488 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_493`. -/
@[expose]
noncomputable def nb078AlphaDummy493 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy486))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_494`. -/
@[expose]
noncomputable def nb078AlphaDummy494 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy486))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_495`. -/
@[expose]
noncomputable def nb078AlphaDummy495 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy488 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_496`. -/
@[expose]
noncomputable def nb078AlphaDummy496 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy488 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_497`. -/
@[expose]
noncomputable def nb078AlphaDummy497 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy493)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy493)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy493))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_498`. -/
@[expose]
noncomputable def nb078AlphaDummy498 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy495 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy495 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy495 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_499`. -/
@[expose]
noncomputable def nb078AlphaDummy499 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_500`. -/
@[expose]
noncomputable def nb078AlphaDummy500 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_501`. -/
@[expose]
noncomputable def nb078AlphaDummy501 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_502`. -/
@[expose]
noncomputable def nb078AlphaDummy502 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_503`. -/
@[expose]
noncomputable def nb078AlphaDummy503 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_504`. -/
@[expose]
noncomputable def nb078AlphaDummy504 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_505`. -/
@[expose]
noncomputable def nb078AlphaDummy505 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy500))
          (Class.cv (nb078AlphaDummy501)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy500)) (Class.cv (nb078AlphaDummy501)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_506`. -/
@[expose]
noncomputable def nb078AlphaDummy506 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy503 g))
          (Class.cv (nb078AlphaDummy504 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy503 g)) (Class.cv (nb078AlphaDummy504 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_507`. -/
@[expose]
noncomputable def nb078AlphaDummy507 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_508`. -/
@[expose]
noncomputable def nb078AlphaDummy508 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy503 g))).fv ∪
      ((Class.cv (nb078AlphaDummy504 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_509`. -/
@[expose]
noncomputable def nb078AlphaDummy509 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy500)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy501)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_510`. -/
@[expose]
noncomputable def nb078AlphaDummy510 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy503 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy504 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_511`. -/
@[expose]
noncomputable def nb078AlphaDummy511 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy500))).fv ∪ ((Class.cv (nb078AlphaDummy500))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_512`. -/
@[expose]
noncomputable def nb078AlphaDummy512 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy503 g))).fv ∪
      ((Class.cv (nb078AlphaDummy503 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_513`. -/
@[expose]
noncomputable def nb078AlphaDummy513 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy501))).fv ∪ ((Class.cv (nb078AlphaDummy501))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_514`. -/
@[expose]
noncomputable def nb078AlphaDummy514 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy504 g))).fv ∪
      ((Class.cv (nb078AlphaDummy504 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_515`. -/
@[expose]
noncomputable def nb078AlphaDummy515 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy485)
          (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
            (Wff.classEq (Class.cv (nb078AlphaDummy485))
              (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy485)
          (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
            (Wff.classEq (Class.cv (nb078AlphaDummy485))
              (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_516`. -/
@[expose]
noncomputable def nb078AlphaDummy516 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy487 g)
          (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy487 g)
          (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_517`. -/
@[expose]
noncomputable def nb078AlphaDummy517 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy486))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_518`. -/
@[expose]
noncomputable def nb078AlphaDummy518 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy488 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_519`. -/
@[expose]
noncomputable def nb078AlphaDummy519 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy486)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy486)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_520`. -/
@[expose]
noncomputable def nb078AlphaDummy520 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy488 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy488 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_521`. -/
@[expose]
noncomputable def nb078AlphaDummy521 : Var :=
  (freshVar (((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
          (Class.cv (nb078AlphaDummy003)))).fv ∪
      ((synCnin (synCrn (Class.cv (nb078AlphaDummy001)))
          (Class.cv (nb078AlphaDummy003)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_522`. -/
@[expose]
noncomputable def nb078AlphaDummy522 (x : Var) (g : Var) : Var :=
  (freshVar (((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv ∪
      ((synCnin (synCrn (Class.cv g)) (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_523`. -/
@[expose]
noncomputable def nb078AlphaDummy523 : Var :=
  (freshVar (((synCrn (Class.cv (nb078AlphaDummy001)))).fv ∪
      ((Class.cv (nb078AlphaDummy003))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_524`. -/
@[expose]
noncomputable def nb078AlphaDummy524 (x : Var) (g : Var) : Var :=
  (freshVar (((synCrn (Class.cv g))).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_525`. -/
@[expose]
noncomputable def nb078AlphaDummy525 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_526`. -/
@[expose]
noncomputable def nb078AlphaDummy526 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_527`. -/
@[expose]
noncomputable def nb078AlphaDummy527 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_528`. -/
@[expose]
noncomputable def nb078AlphaDummy528 (g : Var) : Var :=
  (freshVar (((Class.cv g)).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_529`. -/
@[expose]
noncomputable def nb078AlphaDummy529 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_530`. -/
@[expose]
noncomputable def nb078AlphaDummy530 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy526))).fv ∪ ((Class.cv (nb078AlphaDummy525))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_531`. -/
@[expose]
noncomputable def nb078AlphaDummy531 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy528 g))).fv ∪
      ((Class.cv (nb078AlphaDummy527 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_532`. -/
@[expose]
noncomputable def nb078AlphaDummy532 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy528 g))).fv ∪
      ((Class.cv (nb078AlphaDummy527 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_533`. -/
@[expose]
noncomputable def nb078AlphaDummy533 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCphi (Class.cv (nb078AlphaDummy530)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_534`. -/
@[expose]
noncomputable def nb078AlphaDummy534 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCphi (Class.cv (nb078AlphaDummy532 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_535`. -/
@[expose]
noncomputable def nb078AlphaDummy535 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy529)
          (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
            (Wff.classEq (Class.cv (nb078AlphaDummy529))
              (synCphi (Class.cv (nb078AlphaDummy530))))))).fv ∪
      ((Class.cab (nb078AlphaDummy529)
          (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
            (Wff.classEq (Class.cv (nb078AlphaDummy529))
              (synCphi (Class.cv (nb078AlphaDummy530))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_536`. -/
@[expose]
noncomputable def nb078AlphaDummy536 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy531 g)
          (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
              (synCphi (Class.cv (nb078AlphaDummy532 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy531 g)
          (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
              (synCphi (Class.cv (nb078AlphaDummy532 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_537`. -/
@[expose]
noncomputable def nb078AlphaDummy537 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy530))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_538`. -/
@[expose]
noncomputable def nb078AlphaDummy538 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy530))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_539`. -/
@[expose]
noncomputable def nb078AlphaDummy539 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy532 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_540`. -/
@[expose]
noncomputable def nb078AlphaDummy540 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy532 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_541`. -/
@[expose]
noncomputable def nb078AlphaDummy541 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy537)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy537)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy537))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_542`. -/
@[expose]
noncomputable def nb078AlphaDummy542 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy539 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy539 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy539 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_543`. -/
@[expose]
noncomputable def nb078AlphaDummy543 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_544`. -/
@[expose]
noncomputable def nb078AlphaDummy544 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_545`. -/
@[expose]
noncomputable def nb078AlphaDummy545 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_546`. -/
@[expose]
noncomputable def nb078AlphaDummy546 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_547`. -/
@[expose]
noncomputable def nb078AlphaDummy547 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_548`. -/
@[expose]
noncomputable def nb078AlphaDummy548 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_549`. -/
@[expose]
noncomputable def nb078AlphaDummy549 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy544))
          (Class.cv (nb078AlphaDummy545)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy544)) (Class.cv (nb078AlphaDummy545)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_550`. -/
@[expose]
noncomputable def nb078AlphaDummy550 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy547 g))
          (Class.cv (nb078AlphaDummy548 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy547 g)) (Class.cv (nb078AlphaDummy548 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_551`. -/
@[expose]
noncomputable def nb078AlphaDummy551 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_552`. -/
@[expose]
noncomputable def nb078AlphaDummy552 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy547 g))).fv ∪
      ((Class.cv (nb078AlphaDummy548 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_553`. -/
@[expose]
noncomputable def nb078AlphaDummy553 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy544)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy545)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_554`. -/
@[expose]
noncomputable def nb078AlphaDummy554 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy547 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy548 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_555`. -/
@[expose]
noncomputable def nb078AlphaDummy555 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy544))).fv ∪ ((Class.cv (nb078AlphaDummy544))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_556`. -/
@[expose]
noncomputable def nb078AlphaDummy556 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy547 g))).fv ∪
      ((Class.cv (nb078AlphaDummy547 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_557`. -/
@[expose]
noncomputable def nb078AlphaDummy557 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy545))).fv ∪ ((Class.cv (nb078AlphaDummy545))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_558`. -/
@[expose]
noncomputable def nb078AlphaDummy558 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy548 g))).fv ∪
      ((Class.cv (nb078AlphaDummy548 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_559`. -/
@[expose]
noncomputable def nb078AlphaDummy559 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy529)
          (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
            (Wff.classEq (Class.cv (nb078AlphaDummy529))
              (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy529)
          (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
            (Wff.classEq (Class.cv (nb078AlphaDummy529))
              (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_560`. -/
@[expose]
noncomputable def nb078AlphaDummy560 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy531 g)
          (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy531 g)
          (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_561`. -/
@[expose]
noncomputable def nb078AlphaDummy561 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy530))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_562`. -/
@[expose]
noncomputable def nb078AlphaDummy562 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy532 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_563`. -/
@[expose]
noncomputable def nb078AlphaDummy563 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy530)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy530)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_564`. -/
@[expose]
noncomputable def nb078AlphaDummy564 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy532 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy532 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_565`. -/
@[expose]
noncomputable def nb078AlphaDummy565 : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))) (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_566`. -/
@[expose]
noncomputable def nb078AlphaDummy566 (g : Var) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))
          (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))
          (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_567`. -/
@[expose]
noncomputable def nb078AlphaDummy567 : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv (nb078AlphaDummy001)))
          (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001)))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_568`. -/
@[expose]
noncomputable def nb078AlphaDummy568 (g : Var) : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv g)) (synCcnv (synCcnv (Class.cv g))))).fv ∪
      ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_569`. -/
@[expose]
noncomputable def nb078AlphaDummy569 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_570`. -/
@[expose]
noncomputable def nb078AlphaDummy570 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_571`. -/
@[expose]
noncomputable def nb078AlphaDummy571 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_572`. -/
@[expose]
noncomputable def nb078AlphaDummy572 (g : Var) : Var :=
  (freshVar (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_573`. -/
@[expose]
noncomputable def nb078AlphaDummy573 (g : Var) : Var :=
  (freshVar (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_574`. -/
@[expose]
noncomputable def nb078AlphaDummy574 (g : Var) : Var :=
  (freshVar (((synCcnv (Class.cv g))).fv ∪ ((synCcnv (synCcnv (Class.cv g)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_575`. -/
@[expose]
noncomputable def nb078AlphaDummy575 : Var :=
  (freshVar
    (({(nb078AlphaDummy569)} : Finset Var) ∪ ({(nb078AlphaDummy570)} : Finset Var) ∪
      ((synWex (nb078AlphaDummy571) (synWa (synWbr (Class.cv (nb078AlphaDummy569))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy001))))
              (Class.cv (nb078AlphaDummy571))) (synWbr (Class.cv (nb078AlphaDummy571))
              (synCcnv (Class.cv (nb078AlphaDummy001)))
              (Class.cv (nb078AlphaDummy570)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_576`. -/
@[expose]
noncomputable def nb078AlphaDummy576 (g : Var) : Var :=
  (freshVar (({(nb078AlphaDummy572 g)} : Finset Var) ∪
        ({(nb078AlphaDummy573 g)} : Finset Var) ∪ ((synWex (nb078AlphaDummy574 g) (synWa
            (synWbr (Class.cv (nb078AlphaDummy572 g))
              (synCcnv (synCcnv (Class.cv g))) (Class.cv (nb078AlphaDummy574 g)))
            (synWbr (Class.cv (nb078AlphaDummy574 g)) (synCcnv (Class.cv g))
              (Class.cv (nb078AlphaDummy573 g)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_577`. -/
@[expose]
noncomputable def nb078AlphaDummy577 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_578`. -/
@[expose]
noncomputable def nb078AlphaDummy578 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_579`. -/
@[expose]
noncomputable def nb078AlphaDummy579 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy572 g))).fv ∪
      ((Class.cv (nb078AlphaDummy573 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_580`. -/
@[expose]
noncomputable def nb078AlphaDummy580 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy572 g))).fv ∪
      ((Class.cv (nb078AlphaDummy573 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_581`. -/
@[expose]
noncomputable def nb078AlphaDummy581 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCphi (Class.cv (nb078AlphaDummy578)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_582`. -/
@[expose]
noncomputable def nb078AlphaDummy582 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCphi (Class.cv (nb078AlphaDummy580 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_583`. -/
@[expose]
noncomputable def nb078AlphaDummy583 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy577)
          (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
            (Wff.classEq (Class.cv (nb078AlphaDummy577))
              (synCphi (Class.cv (nb078AlphaDummy578))))))).fv ∪
      ((Class.cab (nb078AlphaDummy577)
          (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
            (Wff.classEq (Class.cv (nb078AlphaDummy577))
              (synCphi (Class.cv (nb078AlphaDummy578))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_584`. -/
@[expose]
noncomputable def nb078AlphaDummy584 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy579 g)
          (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
              (synCphi (Class.cv (nb078AlphaDummy580 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy579 g)
          (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
              (synCphi (Class.cv (nb078AlphaDummy580 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_585`. -/
@[expose]
noncomputable def nb078AlphaDummy585 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy578))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_586`. -/
@[expose]
noncomputable def nb078AlphaDummy586 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy578))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_587`. -/
@[expose]
noncomputable def nb078AlphaDummy587 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy580 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_588`. -/
@[expose]
noncomputable def nb078AlphaDummy588 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy580 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_589`. -/
@[expose]
noncomputable def nb078AlphaDummy589 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy585)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy585)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy585))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_590`. -/
@[expose]
noncomputable def nb078AlphaDummy590 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy587 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy587 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy587 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_591`. -/
@[expose]
noncomputable def nb078AlphaDummy591 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_592`. -/
@[expose]
noncomputable def nb078AlphaDummy592 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_593`. -/
@[expose]
noncomputable def nb078AlphaDummy593 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_594`. -/
@[expose]
noncomputable def nb078AlphaDummy594 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_595`. -/
@[expose]
noncomputable def nb078AlphaDummy595 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_596`. -/
@[expose]
noncomputable def nb078AlphaDummy596 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_597`. -/
@[expose]
noncomputable def nb078AlphaDummy597 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy592))
          (Class.cv (nb078AlphaDummy593)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy592)) (Class.cv (nb078AlphaDummy593)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_598`. -/
@[expose]
noncomputable def nb078AlphaDummy598 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy595 g))
          (Class.cv (nb078AlphaDummy596 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy595 g)) (Class.cv (nb078AlphaDummy596 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_599`. -/
@[expose]
noncomputable def nb078AlphaDummy599 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_600`. -/
@[expose]
noncomputable def nb078AlphaDummy600 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy595 g))).fv ∪
      ((Class.cv (nb078AlphaDummy596 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_601`. -/
@[expose]
noncomputable def nb078AlphaDummy601 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy592)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy593)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_602`. -/
@[expose]
noncomputable def nb078AlphaDummy602 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy595 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy596 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_603`. -/
@[expose]
noncomputable def nb078AlphaDummy603 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy592))).fv ∪ ((Class.cv (nb078AlphaDummy592))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_604`. -/
@[expose]
noncomputable def nb078AlphaDummy604 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy595 g))).fv ∪
      ((Class.cv (nb078AlphaDummy595 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_605`. -/
@[expose]
noncomputable def nb078AlphaDummy605 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy593))).fv ∪ ((Class.cv (nb078AlphaDummy593))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_606`. -/
@[expose]
noncomputable def nb078AlphaDummy606 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy596 g))).fv ∪
      ((Class.cv (nb078AlphaDummy596 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_607`. -/
@[expose]
noncomputable def nb078AlphaDummy607 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy577)
          (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
            (Wff.classEq (Class.cv (nb078AlphaDummy577))
              (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy577)
          (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
            (Wff.classEq (Class.cv (nb078AlphaDummy577))
              (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_608`. -/
@[expose]
noncomputable def nb078AlphaDummy608 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy579 g)
          (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy579 g)
          (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_609`. -/
@[expose]
noncomputable def nb078AlphaDummy609 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy578))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_610`. -/
@[expose]
noncomputable def nb078AlphaDummy610 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy580 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_611`. -/
@[expose]
noncomputable def nb078AlphaDummy611 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy578)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy578)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_612`. -/
@[expose]
noncomputable def nb078AlphaDummy612 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy580 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy580 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_613`. -/
@[expose]
noncomputable def nb078AlphaDummy613 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_614`. -/
@[expose]
noncomputable def nb078AlphaDummy614 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy569))).fv ∪ ((Class.cv (nb078AlphaDummy571))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_615`. -/
@[expose]
noncomputable def nb078AlphaDummy615 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy572 g))).fv ∪
      ((Class.cv (nb078AlphaDummy574 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_616`. -/
@[expose]
noncomputable def nb078AlphaDummy616 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy572 g))).fv ∪
      ((Class.cv (nb078AlphaDummy574 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_617`. -/
@[expose]
noncomputable def nb078AlphaDummy617 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCphi (Class.cv (nb078AlphaDummy614)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_618`. -/
@[expose]
noncomputable def nb078AlphaDummy618 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCphi (Class.cv (nb078AlphaDummy616 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_619`. -/
@[expose]
noncomputable def nb078AlphaDummy619 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy613)
          (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
            (Wff.classEq (Class.cv (nb078AlphaDummy613))
              (synCphi (Class.cv (nb078AlphaDummy614))))))).fv ∪
      ((Class.cab (nb078AlphaDummy613)
          (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
            (Wff.classEq (Class.cv (nb078AlphaDummy613))
              (synCphi (Class.cv (nb078AlphaDummy614))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_620`. -/
@[expose]
noncomputable def nb078AlphaDummy620 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy615 g)
          (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
              (synCphi (Class.cv (nb078AlphaDummy616 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy615 g)
          (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
              (synCphi (Class.cv (nb078AlphaDummy616 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_621`. -/
@[expose]
noncomputable def nb078AlphaDummy621 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy614))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_622`. -/
@[expose]
noncomputable def nb078AlphaDummy622 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy614))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_623`. -/
@[expose]
noncomputable def nb078AlphaDummy623 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy616 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_624`. -/
@[expose]
noncomputable def nb078AlphaDummy624 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy616 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_625`. -/
@[expose]
noncomputable def nb078AlphaDummy625 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy621)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy621)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy621))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_626`. -/
@[expose]
noncomputable def nb078AlphaDummy626 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy623 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy623 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy623 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_627`. -/
@[expose]
noncomputable def nb078AlphaDummy627 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_628`. -/
@[expose]
noncomputable def nb078AlphaDummy628 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_629`. -/
@[expose]
noncomputable def nb078AlphaDummy629 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_630`. -/
@[expose]
noncomputable def nb078AlphaDummy630 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_631`. -/
@[expose]
noncomputable def nb078AlphaDummy631 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_632`. -/
@[expose]
noncomputable def nb078AlphaDummy632 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_633`. -/
@[expose]
noncomputable def nb078AlphaDummy633 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy628))
          (Class.cv (nb078AlphaDummy629)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy628)) (Class.cv (nb078AlphaDummy629)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_634`. -/
@[expose]
noncomputable def nb078AlphaDummy634 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy631 g))
          (Class.cv (nb078AlphaDummy632 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy631 g)) (Class.cv (nb078AlphaDummy632 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_635`. -/
@[expose]
noncomputable def nb078AlphaDummy635 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_636`. -/
@[expose]
noncomputable def nb078AlphaDummy636 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy631 g))).fv ∪
      ((Class.cv (nb078AlphaDummy632 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_637`. -/
@[expose]
noncomputable def nb078AlphaDummy637 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy628)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy629)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_638`. -/
@[expose]
noncomputable def nb078AlphaDummy638 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy631 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy632 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_639`. -/
@[expose]
noncomputable def nb078AlphaDummy639 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy628))).fv ∪ ((Class.cv (nb078AlphaDummy628))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_640`. -/
@[expose]
noncomputable def nb078AlphaDummy640 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy631 g))).fv ∪
      ((Class.cv (nb078AlphaDummy631 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_641`. -/
@[expose]
noncomputable def nb078AlphaDummy641 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy629))).fv ∪ ((Class.cv (nb078AlphaDummy629))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_642`. -/
@[expose]
noncomputable def nb078AlphaDummy642 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy632 g))).fv ∪
      ((Class.cv (nb078AlphaDummy632 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_643`. -/
@[expose]
noncomputable def nb078AlphaDummy643 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy613)
          (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
            (Wff.classEq (Class.cv (nb078AlphaDummy613))
              (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy613)
          (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
            (Wff.classEq (Class.cv (nb078AlphaDummy613))
              (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_644`. -/
@[expose]
noncomputable def nb078AlphaDummy644 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy615 g)
          (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy615 g)
          (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_645`. -/
@[expose]
noncomputable def nb078AlphaDummy645 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy614))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_646`. -/
@[expose]
noncomputable def nb078AlphaDummy646 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy616 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_647`. -/
@[expose]
noncomputable def nb078AlphaDummy647 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy614)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy614)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_648`. -/
@[expose]
noncomputable def nb078AlphaDummy648 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy616 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy616 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_649`. -/
@[expose]
noncomputable def nb078AlphaDummy649 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_650`. -/
@[expose]
noncomputable def nb078AlphaDummy650 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_651`. -/
@[expose]
noncomputable def nb078AlphaDummy651 (g : Var) : Var :=
  (freshVar (((synCcnv (Class.cv g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_652`. -/
@[expose]
noncomputable def nb078AlphaDummy652 (g : Var) : Var :=
  (freshVar (((synCcnv (Class.cv g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_653`. -/
@[expose]
noncomputable def nb078AlphaDummy653 : Var :=
  (freshVar
    (({(nb078AlphaDummy649)} : Finset Var) ∪ ({(nb078AlphaDummy650)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy650)) (synCcnv (Class.cv (nb078AlphaDummy001)))
          (Class.cv (nb078AlphaDummy649)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_654`. -/
@[expose]
noncomputable def nb078AlphaDummy654 (g : Var) : Var :=
  (freshVar (({(nb078AlphaDummy651 g)} : Finset Var) ∪
        ({(nb078AlphaDummy652 g)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy652 g)) (synCcnv (Class.cv g))
          (Class.cv (nb078AlphaDummy651 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_655`. -/
@[expose]
noncomputable def nb078AlphaDummy655 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_656`. -/
@[expose]
noncomputable def nb078AlphaDummy656 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy649))).fv ∪ ((Class.cv (nb078AlphaDummy650))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_657`. -/
@[expose]
noncomputable def nb078AlphaDummy657 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy651 g))).fv ∪
      ((Class.cv (nb078AlphaDummy652 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_658`. -/
@[expose]
noncomputable def nb078AlphaDummy658 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy651 g))).fv ∪
      ((Class.cv (nb078AlphaDummy652 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_659`. -/
@[expose]
noncomputable def nb078AlphaDummy659 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCphi (Class.cv (nb078AlphaDummy656)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_660`. -/
@[expose]
noncomputable def nb078AlphaDummy660 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCphi (Class.cv (nb078AlphaDummy658 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_661`. -/
@[expose]
noncomputable def nb078AlphaDummy661 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy655)
          (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
            (Wff.classEq (Class.cv (nb078AlphaDummy655))
              (synCphi (Class.cv (nb078AlphaDummy656))))))).fv ∪
      ((Class.cab (nb078AlphaDummy655)
          (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
            (Wff.classEq (Class.cv (nb078AlphaDummy655))
              (synCphi (Class.cv (nb078AlphaDummy656))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_662`. -/
@[expose]
noncomputable def nb078AlphaDummy662 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy657 g)
          (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
              (synCphi (Class.cv (nb078AlphaDummy658 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy657 g)
          (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
              (synCphi (Class.cv (nb078AlphaDummy658 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_663`. -/
@[expose]
noncomputable def nb078AlphaDummy663 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy656))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_664`. -/
@[expose]
noncomputable def nb078AlphaDummy664 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy656))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_665`. -/
@[expose]
noncomputable def nb078AlphaDummy665 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy658 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_666`. -/
@[expose]
noncomputable def nb078AlphaDummy666 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy658 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_667`. -/
@[expose]
noncomputable def nb078AlphaDummy667 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy663)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy663)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy663))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_668`. -/
@[expose]
noncomputable def nb078AlphaDummy668 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy665 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy665 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy665 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_669`. -/
@[expose]
noncomputable def nb078AlphaDummy669 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_670`. -/
@[expose]
noncomputable def nb078AlphaDummy670 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_671`. -/
@[expose]
noncomputable def nb078AlphaDummy671 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_672`. -/
@[expose]
noncomputable def nb078AlphaDummy672 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_673`. -/
@[expose]
noncomputable def nb078AlphaDummy673 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_674`. -/
@[expose]
noncomputable def nb078AlphaDummy674 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_675`. -/
@[expose]
noncomputable def nb078AlphaDummy675 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy670))
          (Class.cv (nb078AlphaDummy671)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy670)) (Class.cv (nb078AlphaDummy671)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_676`. -/
@[expose]
noncomputable def nb078AlphaDummy676 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy673 g))
          (Class.cv (nb078AlphaDummy674 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy673 g)) (Class.cv (nb078AlphaDummy674 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_677`. -/
@[expose]
noncomputable def nb078AlphaDummy677 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_678`. -/
@[expose]
noncomputable def nb078AlphaDummy678 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy673 g))).fv ∪
      ((Class.cv (nb078AlphaDummy674 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_679`. -/
@[expose]
noncomputable def nb078AlphaDummy679 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy670)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy671)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_680`. -/
@[expose]
noncomputable def nb078AlphaDummy680 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy673 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy674 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_681`. -/
@[expose]
noncomputable def nb078AlphaDummy681 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy670))).fv ∪ ((Class.cv (nb078AlphaDummy670))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_682`. -/
@[expose]
noncomputable def nb078AlphaDummy682 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy673 g))).fv ∪
      ((Class.cv (nb078AlphaDummy673 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_683`. -/
@[expose]
noncomputable def nb078AlphaDummy683 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy671))).fv ∪ ((Class.cv (nb078AlphaDummy671))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_684`. -/
@[expose]
noncomputable def nb078AlphaDummy684 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy674 g))).fv ∪
      ((Class.cv (nb078AlphaDummy674 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_685`. -/
@[expose]
noncomputable def nb078AlphaDummy685 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy655)
          (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
            (Wff.classEq (Class.cv (nb078AlphaDummy655))
              (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy655)
          (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
            (Wff.classEq (Class.cv (nb078AlphaDummy655))
              (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_686`. -/
@[expose]
noncomputable def nb078AlphaDummy686 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy657 g)
          (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy657 g)
          (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_687`. -/
@[expose]
noncomputable def nb078AlphaDummy687 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy656))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_688`. -/
@[expose]
noncomputable def nb078AlphaDummy688 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy658 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_689`. -/
@[expose]
noncomputable def nb078AlphaDummy689 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy656)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy656)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_690`. -/
@[expose]
noncomputable def nb078AlphaDummy690 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy658 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy658 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_691`. -/
@[expose]
noncomputable def nb078AlphaDummy691 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_692`. -/
@[expose]
noncomputable def nb078AlphaDummy692 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy650))).fv ∪ ((Class.cv (nb078AlphaDummy649))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_693`. -/
@[expose]
noncomputable def nb078AlphaDummy693 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy652 g))).fv ∪
      ((Class.cv (nb078AlphaDummy651 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_694`. -/
@[expose]
noncomputable def nb078AlphaDummy694 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy652 g))).fv ∪
      ((Class.cv (nb078AlphaDummy651 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_695`. -/
@[expose]
noncomputable def nb078AlphaDummy695 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCphi (Class.cv (nb078AlphaDummy692)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_696`. -/
@[expose]
noncomputable def nb078AlphaDummy696 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCphi (Class.cv (nb078AlphaDummy694 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_697`. -/
@[expose]
noncomputable def nb078AlphaDummy697 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy691)
          (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
            (Wff.classEq (Class.cv (nb078AlphaDummy691))
              (synCphi (Class.cv (nb078AlphaDummy692))))))).fv ∪
      ((Class.cab (nb078AlphaDummy691)
          (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
            (Wff.classEq (Class.cv (nb078AlphaDummy691))
              (synCphi (Class.cv (nb078AlphaDummy692))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_698`. -/
@[expose]
noncomputable def nb078AlphaDummy698 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy693 g)
          (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
              (synCphi (Class.cv (nb078AlphaDummy694 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy693 g)
          (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
              (synCphi (Class.cv (nb078AlphaDummy694 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_699`. -/
@[expose]
noncomputable def nb078AlphaDummy699 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy692))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_700`. -/
@[expose]
noncomputable def nb078AlphaDummy700 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy692))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_701`. -/
@[expose]
noncomputable def nb078AlphaDummy701 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy694 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_702`. -/
@[expose]
noncomputable def nb078AlphaDummy702 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy694 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_703`. -/
@[expose]
noncomputable def nb078AlphaDummy703 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy699)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy699)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy699))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_704`. -/
@[expose]
noncomputable def nb078AlphaDummy704 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy701 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy701 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy701 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_705`. -/
@[expose]
noncomputable def nb078AlphaDummy705 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_706`. -/
@[expose]
noncomputable def nb078AlphaDummy706 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_707`. -/
@[expose]
noncomputable def nb078AlphaDummy707 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_708`. -/
@[expose]
noncomputable def nb078AlphaDummy708 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_709`. -/
@[expose]
noncomputable def nb078AlphaDummy709 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_710`. -/
@[expose]
noncomputable def nb078AlphaDummy710 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_711`. -/
@[expose]
noncomputable def nb078AlphaDummy711 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy706))
          (Class.cv (nb078AlphaDummy707)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy706)) (Class.cv (nb078AlphaDummy707)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_712`. -/
@[expose]
noncomputable def nb078AlphaDummy712 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy709 g))
          (Class.cv (nb078AlphaDummy710 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy709 g)) (Class.cv (nb078AlphaDummy710 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_713`. -/
@[expose]
noncomputable def nb078AlphaDummy713 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_714`. -/
@[expose]
noncomputable def nb078AlphaDummy714 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy709 g))).fv ∪
      ((Class.cv (nb078AlphaDummy710 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_715`. -/
@[expose]
noncomputable def nb078AlphaDummy715 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy706)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy707)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_716`. -/
@[expose]
noncomputable def nb078AlphaDummy716 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy709 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy710 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_717`. -/
@[expose]
noncomputable def nb078AlphaDummy717 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy706))).fv ∪ ((Class.cv (nb078AlphaDummy706))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_718`. -/
@[expose]
noncomputable def nb078AlphaDummy718 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy709 g))).fv ∪
      ((Class.cv (nb078AlphaDummy709 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_719`. -/
@[expose]
noncomputable def nb078AlphaDummy719 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy707))).fv ∪ ((Class.cv (nb078AlphaDummy707))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_720`. -/
@[expose]
noncomputable def nb078AlphaDummy720 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy710 g))).fv ∪
      ((Class.cv (nb078AlphaDummy710 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_721`. -/
@[expose]
noncomputable def nb078AlphaDummy721 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy691)
          (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
            (Wff.classEq (Class.cv (nb078AlphaDummy691))
              (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy691)
          (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
            (Wff.classEq (Class.cv (nb078AlphaDummy691))
              (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_722`. -/
@[expose]
noncomputable def nb078AlphaDummy722 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy693 g)
          (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy693 g)
          (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_723`. -/
@[expose]
noncomputable def nb078AlphaDummy723 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy692))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_724`. -/
@[expose]
noncomputable def nb078AlphaDummy724 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy694 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_725`. -/
@[expose]
noncomputable def nb078AlphaDummy725 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy692)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy692)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_726`. -/
@[expose]
noncomputable def nb078AlphaDummy726 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy694 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy694 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_727`. -/
@[expose]
noncomputable def nb078AlphaDummy727 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_728`. -/
@[expose]
noncomputable def nb078AlphaDummy728 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy571))).fv ∪ ((Class.cv (nb078AlphaDummy570))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_729`. -/
@[expose]
noncomputable def nb078AlphaDummy729 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy574 g))).fv ∪
      ((Class.cv (nb078AlphaDummy573 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_730`. -/
@[expose]
noncomputable def nb078AlphaDummy730 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy574 g))).fv ∪
      ((Class.cv (nb078AlphaDummy573 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_731`. -/
@[expose]
noncomputable def nb078AlphaDummy731 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCphi (Class.cv (nb078AlphaDummy728)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_732`. -/
@[expose]
noncomputable def nb078AlphaDummy732 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCphi (Class.cv (nb078AlphaDummy730 g)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_733`. -/
@[expose]
noncomputable def nb078AlphaDummy733 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy727)
          (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
            (Wff.classEq (Class.cv (nb078AlphaDummy727))
              (synCphi (Class.cv (nb078AlphaDummy728))))))).fv ∪
      ((Class.cab (nb078AlphaDummy727)
          (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
            (Wff.classEq (Class.cv (nb078AlphaDummy727))
              (synCphi (Class.cv (nb078AlphaDummy728))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_734`. -/
@[expose]
noncomputable def nb078AlphaDummy734 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy729 g)
          (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
              (synCphi (Class.cv (nb078AlphaDummy730 g))))))).fv ∪
      ((Class.cab (nb078AlphaDummy729 g)
          (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
              (synCphi (Class.cv (nb078AlphaDummy730 g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_735`. -/
@[expose]
noncomputable def nb078AlphaDummy735 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy728))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_736`. -/
@[expose]
noncomputable def nb078AlphaDummy736 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy728))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_737`. -/
@[expose]
noncomputable def nb078AlphaDummy737 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy730 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_738`. -/
@[expose]
noncomputable def nb078AlphaDummy738 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy730 g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_739`. -/
@[expose]
noncomputable def nb078AlphaDummy739 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy735)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy735)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy735))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_740`. -/
@[expose]
noncomputable def nb078AlphaDummy740 (g : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy737 g)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy737 g)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy737 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_741`. -/
@[expose]
noncomputable def nb078AlphaDummy741 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_742`. -/
@[expose]
noncomputable def nb078AlphaDummy742 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_743`. -/
@[expose]
noncomputable def nb078AlphaDummy743 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_744`. -/
@[expose]
noncomputable def nb078AlphaDummy744 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_745`. -/
@[expose]
noncomputable def nb078AlphaDummy745 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_746`. -/
@[expose]
noncomputable def nb078AlphaDummy746 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_747`. -/
@[expose]
noncomputable def nb078AlphaDummy747 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy742))
          (Class.cv (nb078AlphaDummy743)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy742)) (Class.cv (nb078AlphaDummy743)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_748`. -/
@[expose]
noncomputable def nb078AlphaDummy748 (g : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy745 g))
          (Class.cv (nb078AlphaDummy746 g)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy745 g)) (Class.cv (nb078AlphaDummy746 g)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_749`. -/
@[expose]
noncomputable def nb078AlphaDummy749 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_750`. -/
@[expose]
noncomputable def nb078AlphaDummy750 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy745 g))).fv ∪
      ((Class.cv (nb078AlphaDummy746 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_751`. -/
@[expose]
noncomputable def nb078AlphaDummy751 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy742)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy743)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_752`. -/
@[expose]
noncomputable def nb078AlphaDummy752 (g : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy745 g)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy746 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_753`. -/
@[expose]
noncomputable def nb078AlphaDummy753 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy742))).fv ∪ ((Class.cv (nb078AlphaDummy742))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_754`. -/
@[expose]
noncomputable def nb078AlphaDummy754 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy745 g))).fv ∪
      ((Class.cv (nb078AlphaDummy745 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_755`. -/
@[expose]
noncomputable def nb078AlphaDummy755 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy743))).fv ∪ ((Class.cv (nb078AlphaDummy743))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_756`. -/
@[expose]
noncomputable def nb078AlphaDummy756 (g : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy746 g))).fv ∪
      ((Class.cv (nb078AlphaDummy746 g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_757`. -/
@[expose]
noncomputable def nb078AlphaDummy757 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy727)
          (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
            (Wff.classEq (Class.cv (nb078AlphaDummy727))
              (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy727)
          (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
            (Wff.classEq (Class.cv (nb078AlphaDummy727))
              (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_758`. -/
@[expose]
noncomputable def nb078AlphaDummy758 (g : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy729 g)
          (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy729 g)
          (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
            (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
              (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_759`. -/
@[expose]
noncomputable def nb078AlphaDummy759 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy728))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_760`. -/
@[expose]
noncomputable def nb078AlphaDummy760 (g : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy730 g))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_761`. -/
@[expose]
noncomputable def nb078AlphaDummy761 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy728)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy728)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_762`. -/
@[expose]
noncomputable def nb078AlphaDummy762 (g : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy730 g)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy730 g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_763`. -/
@[expose]
noncomputable def nb078AlphaDummy763 : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb078AlphaDummy002))
            (synCcnv (Class.cv (nb078AlphaDummy002)))) (synCid))).fv ∪ ((synCnin
          (synCcom (Class.cv (nb078AlphaDummy002))
            (synCcnv (Class.cv (nb078AlphaDummy002)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_764`. -/
@[expose]
noncomputable def nb078AlphaDummy764 (h : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_765`. -/
@[expose]
noncomputable def nb078AlphaDummy765 : Var :=
  (freshVar (((synCcom (Class.cv (nb078AlphaDummy002))
          (synCcnv (Class.cv (nb078AlphaDummy002))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_766`. -/
@[expose]
noncomputable def nb078AlphaDummy766 (h : Var) : Var :=
  (freshVar (((synCcom (Class.cv h) (synCcnv (Class.cv h)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_767`. -/
@[expose]
noncomputable def nb078AlphaDummy767 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy002))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_768`. -/
@[expose]
noncomputable def nb078AlphaDummy768 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy002))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_769`. -/
@[expose]
noncomputable def nb078AlphaDummy769 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy002))).fv ∪
      ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_770`. -/
@[expose]
noncomputable def nb078AlphaDummy770 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_771`. -/
@[expose]
noncomputable def nb078AlphaDummy771 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_772`. -/
@[expose]
noncomputable def nb078AlphaDummy772 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_773`. -/
@[expose]
noncomputable def nb078AlphaDummy773 : Var :=
  (freshVar
    (({(nb078AlphaDummy767)} : Finset Var) ∪ ({(nb078AlphaDummy768)} : Finset Var) ∪
      ((synWex (nb078AlphaDummy769) (synWa (synWbr (Class.cv (nb078AlphaDummy767))
              (synCcnv (Class.cv (nb078AlphaDummy002))) (Class.cv (nb078AlphaDummy769)))
            (synWbr (Class.cv (nb078AlphaDummy769)) (Class.cv (nb078AlphaDummy002))
              (Class.cv (nb078AlphaDummy768)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_774`. -/
@[expose]
noncomputable def nb078AlphaDummy774 (h : Var) : Var :=
  (freshVar (({(nb078AlphaDummy770 h)} : Finset Var) ∪
        ({(nb078AlphaDummy771 h)} : Finset Var) ∪ ((synWex (nb078AlphaDummy772 h) (synWa
            (synWbr (Class.cv (nb078AlphaDummy770 h)) (synCcnv (Class.cv h))
              (Class.cv (nb078AlphaDummy772 h)))
            (synWbr (Class.cv (nb078AlphaDummy772 h)) (Class.cv h)
              (Class.cv (nb078AlphaDummy771 h)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_775`. -/
@[expose]
noncomputable def nb078AlphaDummy775 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_776`. -/
@[expose]
noncomputable def nb078AlphaDummy776 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_777`. -/
@[expose]
noncomputable def nb078AlphaDummy777 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy770 h))).fv ∪
      ((Class.cv (nb078AlphaDummy771 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_778`. -/
@[expose]
noncomputable def nb078AlphaDummy778 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy770 h))).fv ∪
      ((Class.cv (nb078AlphaDummy771 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_779`. -/
@[expose]
noncomputable def nb078AlphaDummy779 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCphi (Class.cv (nb078AlphaDummy776)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_780`. -/
@[expose]
noncomputable def nb078AlphaDummy780 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCphi (Class.cv (nb078AlphaDummy778 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_781`. -/
@[expose]
noncomputable def nb078AlphaDummy781 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy775)
          (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
            (Wff.classEq (Class.cv (nb078AlphaDummy775))
              (synCphi (Class.cv (nb078AlphaDummy776))))))).fv ∪
      ((Class.cab (nb078AlphaDummy775)
          (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
            (Wff.classEq (Class.cv (nb078AlphaDummy775))
              (synCphi (Class.cv (nb078AlphaDummy776))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_782`. -/
@[expose]
noncomputable def nb078AlphaDummy782 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy777 h)
          (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
              (synCphi (Class.cv (nb078AlphaDummy778 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy777 h)
          (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
              (synCphi (Class.cv (nb078AlphaDummy778 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_783`. -/
@[expose]
noncomputable def nb078AlphaDummy783 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy776))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_784`. -/
@[expose]
noncomputable def nb078AlphaDummy784 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy776))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_785`. -/
@[expose]
noncomputable def nb078AlphaDummy785 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy778 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_786`. -/
@[expose]
noncomputable def nb078AlphaDummy786 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy778 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_787`. -/
@[expose]
noncomputable def nb078AlphaDummy787 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy783)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy783)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy783))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_788`. -/
@[expose]
noncomputable def nb078AlphaDummy788 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy785 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy785 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy785 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_789`. -/
@[expose]
noncomputable def nb078AlphaDummy789 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_790`. -/
@[expose]
noncomputable def nb078AlphaDummy790 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_791`. -/
@[expose]
noncomputable def nb078AlphaDummy791 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_792`. -/
@[expose]
noncomputable def nb078AlphaDummy792 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_793`. -/
@[expose]
noncomputable def nb078AlphaDummy793 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_794`. -/
@[expose]
noncomputable def nb078AlphaDummy794 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_795`. -/
@[expose]
noncomputable def nb078AlphaDummy795 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy790))
          (Class.cv (nb078AlphaDummy791)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy790)) (Class.cv (nb078AlphaDummy791)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_796`. -/
@[expose]
noncomputable def nb078AlphaDummy796 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy793 h))
          (Class.cv (nb078AlphaDummy794 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy793 h)) (Class.cv (nb078AlphaDummy794 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_797`. -/
@[expose]
noncomputable def nb078AlphaDummy797 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_798`. -/
@[expose]
noncomputable def nb078AlphaDummy798 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy793 h))).fv ∪
      ((Class.cv (nb078AlphaDummy794 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_799`. -/
@[expose]
noncomputable def nb078AlphaDummy799 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy790)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy791)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_800`. -/
@[expose]
noncomputable def nb078AlphaDummy800 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy793 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy794 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_801`. -/
@[expose]
noncomputable def nb078AlphaDummy801 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy790))).fv ∪ ((Class.cv (nb078AlphaDummy790))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_802`. -/
@[expose]
noncomputable def nb078AlphaDummy802 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy793 h))).fv ∪
      ((Class.cv (nb078AlphaDummy793 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_803`. -/
@[expose]
noncomputable def nb078AlphaDummy803 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy791))).fv ∪ ((Class.cv (nb078AlphaDummy791))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_804`. -/
@[expose]
noncomputable def nb078AlphaDummy804 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy794 h))).fv ∪
      ((Class.cv (nb078AlphaDummy794 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_805`. -/
@[expose]
noncomputable def nb078AlphaDummy805 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy775)
          (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
            (Wff.classEq (Class.cv (nb078AlphaDummy775))
              (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy775)
          (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
            (Wff.classEq (Class.cv (nb078AlphaDummy775))
              (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_806`. -/
@[expose]
noncomputable def nb078AlphaDummy806 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy777 h)
          (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy777 h)
          (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_807`. -/
@[expose]
noncomputable def nb078AlphaDummy807 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy776))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_808`. -/
@[expose]
noncomputable def nb078AlphaDummy808 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy778 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_809`. -/
@[expose]
noncomputable def nb078AlphaDummy809 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy776)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy776)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_810`. -/
@[expose]
noncomputable def nb078AlphaDummy810 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy778 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy778 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_811`. -/
@[expose]
noncomputable def nb078AlphaDummy811 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_812`. -/
@[expose]
noncomputable def nb078AlphaDummy812 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_813`. -/
@[expose]
noncomputable def nb078AlphaDummy813 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy770 h))).fv ∪
      ((Class.cv (nb078AlphaDummy772 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_814`. -/
@[expose]
noncomputable def nb078AlphaDummy814 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy770 h))).fv ∪
      ((Class.cv (nb078AlphaDummy772 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_815`. -/
@[expose]
noncomputable def nb078AlphaDummy815 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCphi (Class.cv (nb078AlphaDummy812)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_816`. -/
@[expose]
noncomputable def nb078AlphaDummy816 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCphi (Class.cv (nb078AlphaDummy814 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_817`. -/
@[expose]
noncomputable def nb078AlphaDummy817 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy811)
          (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
            (Wff.classEq (Class.cv (nb078AlphaDummy811))
              (synCphi (Class.cv (nb078AlphaDummy812))))))).fv ∪
      ((Class.cab (nb078AlphaDummy811)
          (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
            (Wff.classEq (Class.cv (nb078AlphaDummy811))
              (synCphi (Class.cv (nb078AlphaDummy812))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_818`. -/
@[expose]
noncomputable def nb078AlphaDummy818 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy813 h)
          (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
              (synCphi (Class.cv (nb078AlphaDummy814 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy813 h)
          (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
              (synCphi (Class.cv (nb078AlphaDummy814 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_819`. -/
@[expose]
noncomputable def nb078AlphaDummy819 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy812))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_820`. -/
@[expose]
noncomputable def nb078AlphaDummy820 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy812))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_821`. -/
@[expose]
noncomputable def nb078AlphaDummy821 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy814 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_822`. -/
@[expose]
noncomputable def nb078AlphaDummy822 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy814 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_823`. -/
@[expose]
noncomputable def nb078AlphaDummy823 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy819)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy819)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy819))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_824`. -/
@[expose]
noncomputable def nb078AlphaDummy824 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy821 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy821 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy821 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_825`. -/
@[expose]
noncomputable def nb078AlphaDummy825 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_826`. -/
@[expose]
noncomputable def nb078AlphaDummy826 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_827`. -/
@[expose]
noncomputable def nb078AlphaDummy827 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_828`. -/
@[expose]
noncomputable def nb078AlphaDummy828 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_829`. -/
@[expose]
noncomputable def nb078AlphaDummy829 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_830`. -/
@[expose]
noncomputable def nb078AlphaDummy830 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_831`. -/
@[expose]
noncomputable def nb078AlphaDummy831 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy826))
          (Class.cv (nb078AlphaDummy827)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy826)) (Class.cv (nb078AlphaDummy827)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_832`. -/
@[expose]
noncomputable def nb078AlphaDummy832 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy829 h))
          (Class.cv (nb078AlphaDummy830 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy829 h)) (Class.cv (nb078AlphaDummy830 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_833`. -/
@[expose]
noncomputable def nb078AlphaDummy833 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_834`. -/
@[expose]
noncomputable def nb078AlphaDummy834 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy829 h))).fv ∪
      ((Class.cv (nb078AlphaDummy830 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_835`. -/
@[expose]
noncomputable def nb078AlphaDummy835 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy826)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy827)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_836`. -/
@[expose]
noncomputable def nb078AlphaDummy836 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy829 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy830 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_837`. -/
@[expose]
noncomputable def nb078AlphaDummy837 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy826))).fv ∪ ((Class.cv (nb078AlphaDummy826))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_838`. -/
@[expose]
noncomputable def nb078AlphaDummy838 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy829 h))).fv ∪
      ((Class.cv (nb078AlphaDummy829 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_839`. -/
@[expose]
noncomputable def nb078AlphaDummy839 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy827))).fv ∪ ((Class.cv (nb078AlphaDummy827))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_840`. -/
@[expose]
noncomputable def nb078AlphaDummy840 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy830 h))).fv ∪
      ((Class.cv (nb078AlphaDummy830 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_841`. -/
@[expose]
noncomputable def nb078AlphaDummy841 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy811)
          (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
            (Wff.classEq (Class.cv (nb078AlphaDummy811))
              (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy811)
          (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
            (Wff.classEq (Class.cv (nb078AlphaDummy811))
              (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_842`. -/
@[expose]
noncomputable def nb078AlphaDummy842 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy813 h)
          (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy813 h)
          (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_843`. -/
@[expose]
noncomputable def nb078AlphaDummy843 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy812))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_844`. -/
@[expose]
noncomputable def nb078AlphaDummy844 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy814 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_845`. -/
@[expose]
noncomputable def nb078AlphaDummy845 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy812)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy812)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_846`. -/
@[expose]
noncomputable def nb078AlphaDummy846 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy814 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy814 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_847`. -/
@[expose]
noncomputable def nb078AlphaDummy847 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_848`. -/
@[expose]
noncomputable def nb078AlphaDummy848 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_849`. -/
@[expose]
noncomputable def nb078AlphaDummy849 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_850`. -/
@[expose]
noncomputable def nb078AlphaDummy850 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_851`. -/
@[expose]
noncomputable def nb078AlphaDummy851 : Var :=
  (freshVar
    (({(nb078AlphaDummy847)} : Finset Var) ∪ ({(nb078AlphaDummy848)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy848)) (Class.cv (nb078AlphaDummy002))
          (Class.cv (nb078AlphaDummy847)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_852`. -/
@[expose]
noncomputable def nb078AlphaDummy852 (h : Var) : Var :=
  (freshVar (({(nb078AlphaDummy849 h)} : Finset Var) ∪
        ({(nb078AlphaDummy850 h)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy850 h)) (Class.cv h)
          (Class.cv (nb078AlphaDummy849 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_853`. -/
@[expose]
noncomputable def nb078AlphaDummy853 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_854`. -/
@[expose]
noncomputable def nb078AlphaDummy854 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_855`. -/
@[expose]
noncomputable def nb078AlphaDummy855 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy849 h))).fv ∪
      ((Class.cv (nb078AlphaDummy850 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_856`. -/
@[expose]
noncomputable def nb078AlphaDummy856 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy849 h))).fv ∪
      ((Class.cv (nb078AlphaDummy850 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_857`. -/
@[expose]
noncomputable def nb078AlphaDummy857 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_858`. -/
@[expose]
noncomputable def nb078AlphaDummy858 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_859`. -/
@[expose]
noncomputable def nb078AlphaDummy859 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy853)
          (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
            (Wff.classEq (Class.cv (nb078AlphaDummy853))
              (synCphi (Class.cv (nb078AlphaDummy854))))))).fv ∪
      ((Class.cab (nb078AlphaDummy853)
          (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
            (Wff.classEq (Class.cv (nb078AlphaDummy853))
              (synCphi (Class.cv (nb078AlphaDummy854))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_860`. -/
@[expose]
noncomputable def nb078AlphaDummy860 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy855 h)
          (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
              (synCphi (Class.cv (nb078AlphaDummy856 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy855 h)
          (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
              (synCphi (Class.cv (nb078AlphaDummy856 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_861`. -/
@[expose]
noncomputable def nb078AlphaDummy861 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy854))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_862`. -/
@[expose]
noncomputable def nb078AlphaDummy862 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy854))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_863`. -/
@[expose]
noncomputable def nb078AlphaDummy863 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy856 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_864`. -/
@[expose]
noncomputable def nb078AlphaDummy864 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy856 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_865`. -/
@[expose]
noncomputable def nb078AlphaDummy865 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy861)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy861)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy861))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_866`. -/
@[expose]
noncomputable def nb078AlphaDummy866 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy863 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy863 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy863 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_867`. -/
@[expose]
noncomputable def nb078AlphaDummy867 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_868`. -/
@[expose]
noncomputable def nb078AlphaDummy868 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_869`. -/
@[expose]
noncomputable def nb078AlphaDummy869 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_870`. -/
@[expose]
noncomputable def nb078AlphaDummy870 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_871`. -/
@[expose]
noncomputable def nb078AlphaDummy871 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_872`. -/
@[expose]
noncomputable def nb078AlphaDummy872 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_873`. -/
@[expose]
noncomputable def nb078AlphaDummy873 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy868))
          (Class.cv (nb078AlphaDummy869)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy868)) (Class.cv (nb078AlphaDummy869)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_874`. -/
@[expose]
noncomputable def nb078AlphaDummy874 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy871 h))
          (Class.cv (nb078AlphaDummy872 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy871 h)) (Class.cv (nb078AlphaDummy872 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_875`. -/
@[expose]
noncomputable def nb078AlphaDummy875 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_876`. -/
@[expose]
noncomputable def nb078AlphaDummy876 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy871 h))).fv ∪
      ((Class.cv (nb078AlphaDummy872 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_877`. -/
@[expose]
noncomputable def nb078AlphaDummy877 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy868)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy869)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_878`. -/
@[expose]
noncomputable def nb078AlphaDummy878 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy871 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy872 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_879`. -/
@[expose]
noncomputable def nb078AlphaDummy879 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy868))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_880`. -/
@[expose]
noncomputable def nb078AlphaDummy880 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy871 h))).fv ∪
      ((Class.cv (nb078AlphaDummy871 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_881`. -/
@[expose]
noncomputable def nb078AlphaDummy881 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy869))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_882`. -/
@[expose]
noncomputable def nb078AlphaDummy882 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy872 h))).fv ∪
      ((Class.cv (nb078AlphaDummy872 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_883`. -/
@[expose]
noncomputable def nb078AlphaDummy883 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy853)
          (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
            (Wff.classEq (Class.cv (nb078AlphaDummy853))
              (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy853)
          (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
            (Wff.classEq (Class.cv (nb078AlphaDummy853))
              (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_884`. -/
@[expose]
noncomputable def nb078AlphaDummy884 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy855 h)
          (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy855 h)
          (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_885`. -/
@[expose]
noncomputable def nb078AlphaDummy885 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy854))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_886`. -/
@[expose]
noncomputable def nb078AlphaDummy886 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy856 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_887`. -/
@[expose]
noncomputable def nb078AlphaDummy887 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy854)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy854)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_888`. -/
@[expose]
noncomputable def nb078AlphaDummy888 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy856 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy856 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_889`. -/
@[expose]
noncomputable def nb078AlphaDummy889 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_890`. -/
@[expose]
noncomputable def nb078AlphaDummy890 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_891`. -/
@[expose]
noncomputable def nb078AlphaDummy891 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy850 h))).fv ∪
      ((Class.cv (nb078AlphaDummy849 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_892`. -/
@[expose]
noncomputable def nb078AlphaDummy892 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy850 h))).fv ∪
      ((Class.cv (nb078AlphaDummy849 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_893`. -/
@[expose]
noncomputable def nb078AlphaDummy893 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_894`. -/
@[expose]
noncomputable def nb078AlphaDummy894 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_895`. -/
@[expose]
noncomputable def nb078AlphaDummy895 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy889)
          (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
            (Wff.classEq (Class.cv (nb078AlphaDummy889))
              (synCphi (Class.cv (nb078AlphaDummy890))))))).fv ∪
      ((Class.cab (nb078AlphaDummy889)
          (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
            (Wff.classEq (Class.cv (nb078AlphaDummy889))
              (synCphi (Class.cv (nb078AlphaDummy890))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_896`. -/
@[expose]
noncomputable def nb078AlphaDummy896 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy891 h)
          (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
              (synCphi (Class.cv (nb078AlphaDummy892 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy891 h)
          (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
              (synCphi (Class.cv (nb078AlphaDummy892 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_897`. -/
@[expose]
noncomputable def nb078AlphaDummy897 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy890))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_898`. -/
@[expose]
noncomputable def nb078AlphaDummy898 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy890))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_899`. -/
@[expose]
noncomputable def nb078AlphaDummy899 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy892 h))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
