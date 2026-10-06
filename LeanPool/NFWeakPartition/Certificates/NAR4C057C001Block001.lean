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

/-! Certificates from `NAR4C057C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_000`. -/
@[expose]
noncomputable def nb057AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_001`. -/
@[expose]
noncomputable def nb057AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_002`. -/
@[expose]
noncomputable def nb057AlphaDummy002 : Var :=
  (freshVar
    (({(nb057AlphaDummy001)} : Finset Var) ∪ ({(nb057AlphaDummy000)} : Finset Var) ∪
      ((synWfn (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_003`. -/
@[expose]
noncomputable def nb057AlphaDummy003 (f : Var) (a : Var) : Var :=
  (freshVar (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ((synWfn (Class.cv f) (Class.cv a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_004`. -/
@[expose]
noncomputable def nb057AlphaDummy004 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_005`. -/
@[expose]
noncomputable def nb057AlphaDummy005 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_006`. -/
@[expose]
noncomputable def nb057AlphaDummy006 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_007`. -/
@[expose]
noncomputable def nb057AlphaDummy007 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_008`. -/
@[expose]
noncomputable def nb057AlphaDummy008 : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCphi (Class.cv (nb057AlphaDummy005)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_009`. -/
@[expose]
noncomputable def nb057AlphaDummy009 (f : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCphi (Class.cv (nb057AlphaDummy007 f a)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_010`. -/
@[expose]
noncomputable def nb057AlphaDummy010 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy004)
          (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
            (Wff.classEq (Class.cv (nb057AlphaDummy004))
              (synCphi (Class.cv (nb057AlphaDummy005))))))).fv ∪
      ((Class.cab (nb057AlphaDummy004)
          (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
            (Wff.classEq (Class.cv (nb057AlphaDummy004))
              (synCphi (Class.cv (nb057AlphaDummy005))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_011`. -/
@[expose]
noncomputable def nb057AlphaDummy011 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy006 f a)
          (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
            (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
              (synCphi (Class.cv (nb057AlphaDummy007 f a))))))).fv ∪
      ((Class.cab (nb057AlphaDummy006 f a) (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
            (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
              (synCphi (Class.cv (nb057AlphaDummy007 f a))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_012`. -/
@[expose]
noncomputable def nb057AlphaDummy012 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy005))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_013`. -/
@[expose]
noncomputable def nb057AlphaDummy013 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy005))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_014`. -/
@[expose]
noncomputable def nb057AlphaDummy014 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy007 f a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_015`. -/
@[expose]
noncomputable def nb057AlphaDummy015 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy007 f a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_016`. -/
@[expose]
noncomputable def nb057AlphaDummy016 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy012)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy012)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy012))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_017`. -/
@[expose]
noncomputable def nb057AlphaDummy017 (f : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy014 f a)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy014 f a)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy014 f a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_018`. -/
@[expose]
noncomputable def nb057AlphaDummy018 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_019`. -/
@[expose]
noncomputable def nb057AlphaDummy019 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_020`. -/
@[expose]
noncomputable def nb057AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_021`. -/
@[expose]
noncomputable def nb057AlphaDummy021 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_022`. -/
@[expose]
noncomputable def nb057AlphaDummy022 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_023`. -/
@[expose]
noncomputable def nb057AlphaDummy023 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_024`. -/
@[expose]
noncomputable def nb057AlphaDummy024 : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy019))
          (Class.cv (nb057AlphaDummy020)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy019)) (Class.cv (nb057AlphaDummy020)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_025`. -/
@[expose]
noncomputable def nb057AlphaDummy025 (f : Var) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy022 f a))
          (Class.cv (nb057AlphaDummy023 f a)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy022 f a))
          (Class.cv (nb057AlphaDummy023 f a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_026`. -/
@[expose]
noncomputable def nb057AlphaDummy026 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_027`. -/
@[expose]
noncomputable def nb057AlphaDummy027 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
      ((Class.cv (nb057AlphaDummy023 f a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_028`. -/
@[expose]
noncomputable def nb057AlphaDummy028 : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy019)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy020)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_029`. -/
@[expose]
noncomputable def nb057AlphaDummy029 (f : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy022 f a)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy023 f a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_030`. -/
@[expose]
noncomputable def nb057AlphaDummy030 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy019))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_031`. -/
@[expose]
noncomputable def nb057AlphaDummy031 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
      ((Class.cv (nb057AlphaDummy022 f a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_032`. -/
@[expose]
noncomputable def nb057AlphaDummy032 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy020))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_033`. -/
@[expose]
noncomputable def nb057AlphaDummy033 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy023 f a))).fv ∪
      ((Class.cv (nb057AlphaDummy023 f a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_034`. -/
@[expose]
noncomputable def nb057AlphaDummy034 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy004)
          (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
            (Wff.classEq (Class.cv (nb057AlphaDummy004))
              (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy004)
          (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
            (Wff.classEq (Class.cv (nb057AlphaDummy004))
              (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_035`. -/
@[expose]
noncomputable def nb057AlphaDummy035 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy006 f a)
          (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
            (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
              (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy006 f a)
          (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
            (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
              (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_036`. -/
@[expose]
noncomputable def nb057AlphaDummy036 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy005))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_037`. -/
@[expose]
noncomputable def nb057AlphaDummy037 (f : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy007 f a))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_038`. -/
@[expose]
noncomputable def nb057AlphaDummy038 : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy005)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy005)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_039`. -/
@[expose]
noncomputable def nb057AlphaDummy039 (f : Var) (a : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy007 f a)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy007 f a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_040`. -/
@[expose]
noncomputable def nb057AlphaDummy040 : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb057AlphaDummy001))
            (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))).fv ∪ ((synCnin
          (synCcom (Class.cv (nb057AlphaDummy001))
            (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_041`. -/
@[expose]
noncomputable def nb057AlphaDummy041 (f : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_042`. -/
@[expose]
noncomputable def nb057AlphaDummy042 : Var :=
  (freshVar (((synCcom (Class.cv (nb057AlphaDummy001))
          (synCcnv (Class.cv (nb057AlphaDummy001))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_043`. -/
@[expose]
noncomputable def nb057AlphaDummy043 (f : Var) : Var :=
  (freshVar (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_044`. -/
@[expose]
noncomputable def nb057AlphaDummy044 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy001))).fv ∪
      ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_045`. -/
@[expose]
noncomputable def nb057AlphaDummy045 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy001))).fv ∪
      ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_046`. -/
@[expose]
noncomputable def nb057AlphaDummy046 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy001))).fv ∪
      ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_047`. -/
@[expose]
noncomputable def nb057AlphaDummy047 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_048`. -/
@[expose]
noncomputable def nb057AlphaDummy048 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_049`. -/
@[expose]
noncomputable def nb057AlphaDummy049 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_050`. -/
@[expose]
noncomputable def nb057AlphaDummy050 : Var :=
  (freshVar
    (({(nb057AlphaDummy044)} : Finset Var) ∪ ({(nb057AlphaDummy045)} : Finset Var) ∪
      ((synWex (nb057AlphaDummy046) (synWa (synWbr (Class.cv (nb057AlphaDummy044))
              (synCcnv (Class.cv (nb057AlphaDummy001))) (Class.cv (nb057AlphaDummy046)))
            (synWbr (Class.cv (nb057AlphaDummy046)) (Class.cv (nb057AlphaDummy001))
              (Class.cv (nb057AlphaDummy045)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_051`. -/
@[expose]
noncomputable def nb057AlphaDummy051 (f : Var) : Var :=
  (freshVar (({(nb057AlphaDummy047 f)} : Finset Var) ∪
        ({(nb057AlphaDummy048 f)} : Finset Var) ∪ ((synWex (nb057AlphaDummy049 f) (synWa
            (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
              (Class.cv (nb057AlphaDummy049 f)))
            (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
              (Class.cv (nb057AlphaDummy048 f)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_052`. -/
@[expose]
noncomputable def nb057AlphaDummy052 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_053`. -/
@[expose]
noncomputable def nb057AlphaDummy053 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_054`. -/
@[expose]
noncomputable def nb057AlphaDummy054 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy047 f))).fv ∪
      ((Class.cv (nb057AlphaDummy048 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_055`. -/
@[expose]
noncomputable def nb057AlphaDummy055 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy047 f))).fv ∪
      ((Class.cv (nb057AlphaDummy048 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_056`. -/
@[expose]
noncomputable def nb057AlphaDummy056 : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCphi (Class.cv (nb057AlphaDummy053)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_057`. -/
@[expose]
noncomputable def nb057AlphaDummy057 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCphi (Class.cv (nb057AlphaDummy055 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_058`. -/
@[expose]
noncomputable def nb057AlphaDummy058 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy052)
          (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
            (Wff.classEq (Class.cv (nb057AlphaDummy052))
              (synCphi (Class.cv (nb057AlphaDummy053))))))).fv ∪
      ((Class.cab (nb057AlphaDummy052)
          (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
            (Wff.classEq (Class.cv (nb057AlphaDummy052))
              (synCphi (Class.cv (nb057AlphaDummy053))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_059`. -/
@[expose]
noncomputable def nb057AlphaDummy059 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy054 f)
          (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
              (synCphi (Class.cv (nb057AlphaDummy055 f))))))).fv ∪
      ((Class.cab (nb057AlphaDummy054 f)
          (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
              (synCphi (Class.cv (nb057AlphaDummy055 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_060`. -/
@[expose]
noncomputable def nb057AlphaDummy060 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy053))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_061`. -/
@[expose]
noncomputable def nb057AlphaDummy061 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy053))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_062`. -/
@[expose]
noncomputable def nb057AlphaDummy062 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy055 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_063`. -/
@[expose]
noncomputable def nb057AlphaDummy063 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy055 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_064`. -/
@[expose]
noncomputable def nb057AlphaDummy064 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy060)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy060)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy060))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_065`. -/
@[expose]
noncomputable def nb057AlphaDummy065 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy062 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy062 f)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy062 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_066`. -/
@[expose]
noncomputable def nb057AlphaDummy066 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_067`. -/
@[expose]
noncomputable def nb057AlphaDummy067 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_068`. -/
@[expose]
noncomputable def nb057AlphaDummy068 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_069`. -/
@[expose]
noncomputable def nb057AlphaDummy069 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_070`. -/
@[expose]
noncomputable def nb057AlphaDummy070 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_071`. -/
@[expose]
noncomputable def nb057AlphaDummy071 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_072`. -/
@[expose]
noncomputable def nb057AlphaDummy072 : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy067))
          (Class.cv (nb057AlphaDummy068)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_073`. -/
@[expose]
noncomputable def nb057AlphaDummy073 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy070 f))
          (Class.cv (nb057AlphaDummy071 f)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy070 f)) (Class.cv (nb057AlphaDummy071 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_074`. -/
@[expose]
noncomputable def nb057AlphaDummy074 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_075`. -/
@[expose]
noncomputable def nb057AlphaDummy075 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy070 f))).fv ∪
      ((Class.cv (nb057AlphaDummy071 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_076`. -/
@[expose]
noncomputable def nb057AlphaDummy076 : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy067)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy068)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_077`. -/
@[expose]
noncomputable def nb057AlphaDummy077 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy070 f)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy071 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_078`. -/
@[expose]
noncomputable def nb057AlphaDummy078 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy067))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_079`. -/
@[expose]
noncomputable def nb057AlphaDummy079 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy070 f))).fv ∪
      ((Class.cv (nb057AlphaDummy070 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_080`. -/
@[expose]
noncomputable def nb057AlphaDummy080 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy068))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_081`. -/
@[expose]
noncomputable def nb057AlphaDummy081 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy071 f))).fv ∪
      ((Class.cv (nb057AlphaDummy071 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_082`. -/
@[expose]
noncomputable def nb057AlphaDummy082 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy052)
          (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
            (Wff.classEq (Class.cv (nb057AlphaDummy052))
              (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy052)
          (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
            (Wff.classEq (Class.cv (nb057AlphaDummy052))
              (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_083`. -/
@[expose]
noncomputable def nb057AlphaDummy083 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy054 f)
          (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy054 f)
          (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_084`. -/
@[expose]
noncomputable def nb057AlphaDummy084 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy053))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_085`. -/
@[expose]
noncomputable def nb057AlphaDummy085 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy055 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_086`. -/
@[expose]
noncomputable def nb057AlphaDummy086 : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy053)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy053)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_087`. -/
@[expose]
noncomputable def nb057AlphaDummy087 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy055 f)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy055 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_088`. -/
@[expose]
noncomputable def nb057AlphaDummy088 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_089`. -/
@[expose]
noncomputable def nb057AlphaDummy089 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_090`. -/
@[expose]
noncomputable def nb057AlphaDummy090 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy047 f))).fv ∪
      ((Class.cv (nb057AlphaDummy049 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_091`. -/
@[expose]
noncomputable def nb057AlphaDummy091 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy047 f))).fv ∪
      ((Class.cv (nb057AlphaDummy049 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_092`. -/
@[expose]
noncomputable def nb057AlphaDummy092 : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCphi (Class.cv (nb057AlphaDummy089)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_093`. -/
@[expose]
noncomputable def nb057AlphaDummy093 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCphi (Class.cv (nb057AlphaDummy091 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_094`. -/
@[expose]
noncomputable def nb057AlphaDummy094 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy088)
          (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
            (Wff.classEq (Class.cv (nb057AlphaDummy088))
              (synCphi (Class.cv (nb057AlphaDummy089))))))).fv ∪
      ((Class.cab (nb057AlphaDummy088)
          (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
            (Wff.classEq (Class.cv (nb057AlphaDummy088))
              (synCphi (Class.cv (nb057AlphaDummy089))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_095`. -/
@[expose]
noncomputable def nb057AlphaDummy095 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy090 f)
          (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
              (synCphi (Class.cv (nb057AlphaDummy091 f))))))).fv ∪
      ((Class.cab (nb057AlphaDummy090 f)
          (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
              (synCphi (Class.cv (nb057AlphaDummy091 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_096`. -/
@[expose]
noncomputable def nb057AlphaDummy096 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy089))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_097`. -/
@[expose]
noncomputable def nb057AlphaDummy097 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy089))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_098`. -/
@[expose]
noncomputable def nb057AlphaDummy098 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy091 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_099`. -/
@[expose]
noncomputable def nb057AlphaDummy099 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy091 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_100`. -/
@[expose]
noncomputable def nb057AlphaDummy100 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy096)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy096)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy096))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_101`. -/
@[expose]
noncomputable def nb057AlphaDummy101 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy098 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy098 f)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy098 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_102`. -/
@[expose]
noncomputable def nb057AlphaDummy102 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_103`. -/
@[expose]
noncomputable def nb057AlphaDummy103 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_104`. -/
@[expose]
noncomputable def nb057AlphaDummy104 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_105`. -/
@[expose]
noncomputable def nb057AlphaDummy105 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_106`. -/
@[expose]
noncomputable def nb057AlphaDummy106 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_107`. -/
@[expose]
noncomputable def nb057AlphaDummy107 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_108`. -/
@[expose]
noncomputable def nb057AlphaDummy108 : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy103))
          (Class.cv (nb057AlphaDummy104)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_109`. -/
@[expose]
noncomputable def nb057AlphaDummy109 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy106 f))
          (Class.cv (nb057AlphaDummy107 f)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy106 f)) (Class.cv (nb057AlphaDummy107 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_110`. -/
@[expose]
noncomputable def nb057AlphaDummy110 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_111`. -/
@[expose]
noncomputable def nb057AlphaDummy111 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy106 f))).fv ∪
      ((Class.cv (nb057AlphaDummy107 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_112`. -/
@[expose]
noncomputable def nb057AlphaDummy112 : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy103)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy104)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_113`. -/
@[expose]
noncomputable def nb057AlphaDummy113 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy106 f)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy107 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_114`. -/
@[expose]
noncomputable def nb057AlphaDummy114 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy103))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_115`. -/
@[expose]
noncomputable def nb057AlphaDummy115 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy106 f))).fv ∪
      ((Class.cv (nb057AlphaDummy106 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_116`. -/
@[expose]
noncomputable def nb057AlphaDummy116 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy104))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_117`. -/
@[expose]
noncomputable def nb057AlphaDummy117 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy107 f))).fv ∪
      ((Class.cv (nb057AlphaDummy107 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_118`. -/
@[expose]
noncomputable def nb057AlphaDummy118 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy088)
          (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
            (Wff.classEq (Class.cv (nb057AlphaDummy088))
              (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy088)
          (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
            (Wff.classEq (Class.cv (nb057AlphaDummy088))
              (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_119`. -/
@[expose]
noncomputable def nb057AlphaDummy119 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy090 f)
          (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy090 f)
          (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_120`. -/
@[expose]
noncomputable def nb057AlphaDummy120 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy089))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_121`. -/
@[expose]
noncomputable def nb057AlphaDummy121 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy091 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_122`. -/
@[expose]
noncomputable def nb057AlphaDummy122 : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy089)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy089)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_123`. -/
@[expose]
noncomputable def nb057AlphaDummy123 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy091 f)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy091 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_124`. -/
@[expose]
noncomputable def nb057AlphaDummy124 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_125`. -/
@[expose]
noncomputable def nb057AlphaDummy125 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_126`. -/
@[expose]
noncomputable def nb057AlphaDummy126 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_127`. -/
@[expose]
noncomputable def nb057AlphaDummy127 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_128`. -/
@[expose]
noncomputable def nb057AlphaDummy128 : Var :=
  (freshVar
    (({(nb057AlphaDummy124)} : Finset Var) ∪ ({(nb057AlphaDummy125)} : Finset Var) ∪
      ((synWbr (Class.cv (nb057AlphaDummy125)) (Class.cv (nb057AlphaDummy001))
          (Class.cv (nb057AlphaDummy124)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_129`. -/
@[expose]
noncomputable def nb057AlphaDummy129 (f : Var) : Var :=
  (freshVar (({(nb057AlphaDummy126 f)} : Finset Var) ∪
        ({(nb057AlphaDummy127 f)} : Finset Var) ∪
      ((synWbr (Class.cv (nb057AlphaDummy127 f)) (Class.cv f)
          (Class.cv (nb057AlphaDummy126 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_130`. -/
@[expose]
noncomputable def nb057AlphaDummy130 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_131`. -/
@[expose]
noncomputable def nb057AlphaDummy131 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_132`. -/
@[expose]
noncomputable def nb057AlphaDummy132 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy126 f))).fv ∪
      ((Class.cv (nb057AlphaDummy127 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_133`. -/
@[expose]
noncomputable def nb057AlphaDummy133 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy126 f))).fv ∪
      ((Class.cv (nb057AlphaDummy127 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_134`. -/
@[expose]
noncomputable def nb057AlphaDummy134 : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCphi (Class.cv (nb057AlphaDummy131)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_135`. -/
@[expose]
noncomputable def nb057AlphaDummy135 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCphi (Class.cv (nb057AlphaDummy133 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_136`. -/
@[expose]
noncomputable def nb057AlphaDummy136 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy130)
          (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
            (Wff.classEq (Class.cv (nb057AlphaDummy130))
              (synCphi (Class.cv (nb057AlphaDummy131))))))).fv ∪
      ((Class.cab (nb057AlphaDummy130)
          (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
            (Wff.classEq (Class.cv (nb057AlphaDummy130))
              (synCphi (Class.cv (nb057AlphaDummy131))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_137`. -/
@[expose]
noncomputable def nb057AlphaDummy137 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy132 f)
          (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
              (synCphi (Class.cv (nb057AlphaDummy133 f))))))).fv ∪
      ((Class.cab (nb057AlphaDummy132 f)
          (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
              (synCphi (Class.cv (nb057AlphaDummy133 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_138`. -/
@[expose]
noncomputable def nb057AlphaDummy138 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy131))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_139`. -/
@[expose]
noncomputable def nb057AlphaDummy139 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy131))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_140`. -/
@[expose]
noncomputable def nb057AlphaDummy140 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy133 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_141`. -/
@[expose]
noncomputable def nb057AlphaDummy141 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy133 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_142`. -/
@[expose]
noncomputable def nb057AlphaDummy142 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy138)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy138)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy138))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_143`. -/
@[expose]
noncomputable def nb057AlphaDummy143 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy140 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy140 f)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy140 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_144`. -/
@[expose]
noncomputable def nb057AlphaDummy144 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_145`. -/
@[expose]
noncomputable def nb057AlphaDummy145 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_146`. -/
@[expose]
noncomputable def nb057AlphaDummy146 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_147`. -/
@[expose]
noncomputable def nb057AlphaDummy147 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_148`. -/
@[expose]
noncomputable def nb057AlphaDummy148 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_149`. -/
@[expose]
noncomputable def nb057AlphaDummy149 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) 2)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_150`. -/
@[expose]
noncomputable def nb057AlphaDummy150 : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy145))
          (Class.cv (nb057AlphaDummy146)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_151`. -/
@[expose]
noncomputable def nb057AlphaDummy151 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy148 f))
          (Class.cv (nb057AlphaDummy149 f)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy148 f)) (Class.cv (nb057AlphaDummy149 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_152`. -/
@[expose]
noncomputable def nb057AlphaDummy152 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_153`. -/
@[expose]
noncomputable def nb057AlphaDummy153 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy148 f))).fv ∪
      ((Class.cv (nb057AlphaDummy149 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_154`. -/
@[expose]
noncomputable def nb057AlphaDummy154 : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy145)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy146)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_155`. -/
@[expose]
noncomputable def nb057AlphaDummy155 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy148 f)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy149 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_156`. -/
@[expose]
noncomputable def nb057AlphaDummy156 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy145))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_157`. -/
@[expose]
noncomputable def nb057AlphaDummy157 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy148 f))).fv ∪
      ((Class.cv (nb057AlphaDummy148 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_158`. -/
@[expose]
noncomputable def nb057AlphaDummy158 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy146))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_159`. -/
@[expose]
noncomputable def nb057AlphaDummy159 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy149 f))).fv ∪
      ((Class.cv (nb057AlphaDummy149 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_160`. -/
@[expose]
noncomputable def nb057AlphaDummy160 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy130)
          (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
            (Wff.classEq (Class.cv (nb057AlphaDummy130))
              (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy130)
          (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
            (Wff.classEq (Class.cv (nb057AlphaDummy130))
              (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_161`. -/
@[expose]
noncomputable def nb057AlphaDummy161 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy132 f)
          (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy132 f)
          (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_162`. -/
@[expose]
noncomputable def nb057AlphaDummy162 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy131))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_163`. -/
@[expose]
noncomputable def nb057AlphaDummy163 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy133 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_164`. -/
@[expose]
noncomputable def nb057AlphaDummy164 : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy131)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy131)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_165`. -/
@[expose]
noncomputable def nb057AlphaDummy165 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy133 f)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy133 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_166`. -/
@[expose]
noncomputable def nb057AlphaDummy166 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_167`. -/
@[expose]
noncomputable def nb057AlphaDummy167 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_168`. -/
@[expose]
noncomputable def nb057AlphaDummy168 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy127 f))).fv ∪
      ((Class.cv (nb057AlphaDummy126 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_169`. -/
@[expose]
noncomputable def nb057AlphaDummy169 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy127 f))).fv ∪
      ((Class.cv (nb057AlphaDummy126 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_170`. -/
@[expose]
noncomputable def nb057AlphaDummy170 : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCphi (Class.cv (nb057AlphaDummy167)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_171`. -/
@[expose]
noncomputable def nb057AlphaDummy171 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCphi (Class.cv (nb057AlphaDummy169 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_172`. -/
@[expose]
noncomputable def nb057AlphaDummy172 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy166)
          (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
            (Wff.classEq (Class.cv (nb057AlphaDummy166))
              (synCphi (Class.cv (nb057AlphaDummy167))))))).fv ∪
      ((Class.cab (nb057AlphaDummy166)
          (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
            (Wff.classEq (Class.cv (nb057AlphaDummy166))
              (synCphi (Class.cv (nb057AlphaDummy167))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_173`. -/
@[expose]
noncomputable def nb057AlphaDummy173 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy168 f)
          (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
              (synCphi (Class.cv (nb057AlphaDummy169 f))))))).fv ∪
      ((Class.cab (nb057AlphaDummy168 f)
          (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
              (synCphi (Class.cv (nb057AlphaDummy169 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_174`. -/
@[expose]
noncomputable def nb057AlphaDummy174 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy167))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_175`. -/
@[expose]
noncomputable def nb057AlphaDummy175 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy167))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_176`. -/
@[expose]
noncomputable def nb057AlphaDummy176 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy169 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_177`. -/
@[expose]
noncomputable def nb057AlphaDummy177 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy169 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_178`. -/
@[expose]
noncomputable def nb057AlphaDummy178 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy174)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy174)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy174))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_179`. -/
@[expose]
noncomputable def nb057AlphaDummy179 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy176 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy176 f)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy176 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_180`. -/
@[expose]
noncomputable def nb057AlphaDummy180 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_181`. -/
@[expose]
noncomputable def nb057AlphaDummy181 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_182`. -/
@[expose]
noncomputable def nb057AlphaDummy182 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_183`. -/
@[expose]
noncomputable def nb057AlphaDummy183 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_184`. -/
@[expose]
noncomputable def nb057AlphaDummy184 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_185`. -/
@[expose]
noncomputable def nb057AlphaDummy185 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_186`. -/
@[expose]
noncomputable def nb057AlphaDummy186 : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy181))
          (Class.cv (nb057AlphaDummy182)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_187`. -/
@[expose]
noncomputable def nb057AlphaDummy187 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy184 f))
          (Class.cv (nb057AlphaDummy185 f)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy184 f)) (Class.cv (nb057AlphaDummy185 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_188`. -/
@[expose]
noncomputable def nb057AlphaDummy188 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_189`. -/
@[expose]
noncomputable def nb057AlphaDummy189 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy184 f))).fv ∪
      ((Class.cv (nb057AlphaDummy185 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_190`. -/
@[expose]
noncomputable def nb057AlphaDummy190 : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy181)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy182)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_191`. -/
@[expose]
noncomputable def nb057AlphaDummy191 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy184 f)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy185 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_192`. -/
@[expose]
noncomputable def nb057AlphaDummy192 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy181))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_193`. -/
@[expose]
noncomputable def nb057AlphaDummy193 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy184 f))).fv ∪
      ((Class.cv (nb057AlphaDummy184 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_194`. -/
@[expose]
noncomputable def nb057AlphaDummy194 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy182))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_195`. -/
@[expose]
noncomputable def nb057AlphaDummy195 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy185 f))).fv ∪
      ((Class.cv (nb057AlphaDummy185 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_196`. -/
@[expose]
noncomputable def nb057AlphaDummy196 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy166)
          (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
            (Wff.classEq (Class.cv (nb057AlphaDummy166))
              (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy166)
          (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
            (Wff.classEq (Class.cv (nb057AlphaDummy166))
              (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_197`. -/
@[expose]
noncomputable def nb057AlphaDummy197 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy168 f)
          (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy168 f)
          (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_198`. -/
@[expose]
noncomputable def nb057AlphaDummy198 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy167))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_199`. -/
@[expose]
noncomputable def nb057AlphaDummy199 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy169 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_200`. -/
@[expose]
noncomputable def nb057AlphaDummy200 : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy167)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy167)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_201`. -/
@[expose]
noncomputable def nb057AlphaDummy201 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy169 f)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy169 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_202`. -/
@[expose]
noncomputable def nb057AlphaDummy202 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_203`. -/
@[expose]
noncomputable def nb057AlphaDummy203 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_204`. -/
@[expose]
noncomputable def nb057AlphaDummy204 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy049 f))).fv ∪
      ((Class.cv (nb057AlphaDummy048 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_205`. -/
@[expose]
noncomputable def nb057AlphaDummy205 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy049 f))).fv ∪
      ((Class.cv (nb057AlphaDummy048 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_206`. -/
@[expose]
noncomputable def nb057AlphaDummy206 : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCphi (Class.cv (nb057AlphaDummy203)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_207`. -/
@[expose]
noncomputable def nb057AlphaDummy207 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCphi (Class.cv (nb057AlphaDummy205 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_208`. -/
@[expose]
noncomputable def nb057AlphaDummy208 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy202)
          (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
            (Wff.classEq (Class.cv (nb057AlphaDummy202))
              (synCphi (Class.cv (nb057AlphaDummy203))))))).fv ∪
      ((Class.cab (nb057AlphaDummy202)
          (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
            (Wff.classEq (Class.cv (nb057AlphaDummy202))
              (synCphi (Class.cv (nb057AlphaDummy203))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_209`. -/
@[expose]
noncomputable def nb057AlphaDummy209 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy204 f)
          (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
              (synCphi (Class.cv (nb057AlphaDummy205 f))))))).fv ∪
      ((Class.cab (nb057AlphaDummy204 f)
          (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
              (synCphi (Class.cv (nb057AlphaDummy205 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_210`. -/
@[expose]
noncomputable def nb057AlphaDummy210 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy203))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_211`. -/
@[expose]
noncomputable def nb057AlphaDummy211 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy203))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_212`. -/
@[expose]
noncomputable def nb057AlphaDummy212 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy205 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_213`. -/
@[expose]
noncomputable def nb057AlphaDummy213 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy205 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_214`. -/
@[expose]
noncomputable def nb057AlphaDummy214 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy210)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy210)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy210))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_215`. -/
@[expose]
noncomputable def nb057AlphaDummy215 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy212 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy212 f)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy212 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_216`. -/
@[expose]
noncomputable def nb057AlphaDummy216 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_217`. -/
@[expose]
noncomputable def nb057AlphaDummy217 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_218`. -/
@[expose]
noncomputable def nb057AlphaDummy218 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_219`. -/
@[expose]
noncomputable def nb057AlphaDummy219 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_220`. -/
@[expose]
noncomputable def nb057AlphaDummy220 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_221`. -/
@[expose]
noncomputable def nb057AlphaDummy221 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_222`. -/
@[expose]
noncomputable def nb057AlphaDummy222 : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy217))
          (Class.cv (nb057AlphaDummy218)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_223`. -/
@[expose]
noncomputable def nb057AlphaDummy223 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy220 f))
          (Class.cv (nb057AlphaDummy221 f)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy220 f)) (Class.cv (nb057AlphaDummy221 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_224`. -/
@[expose]
noncomputable def nb057AlphaDummy224 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_225`. -/
@[expose]
noncomputable def nb057AlphaDummy225 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy220 f))).fv ∪
      ((Class.cv (nb057AlphaDummy221 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_226`. -/
@[expose]
noncomputable def nb057AlphaDummy226 : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy217)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy218)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_227`. -/
@[expose]
noncomputable def nb057AlphaDummy227 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy220 f)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy221 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_228`. -/
@[expose]
noncomputable def nb057AlphaDummy228 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy217))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_229`. -/
@[expose]
noncomputable def nb057AlphaDummy229 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy220 f))).fv ∪
      ((Class.cv (nb057AlphaDummy220 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_230`. -/
@[expose]
noncomputable def nb057AlphaDummy230 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy218))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_231`. -/
@[expose]
noncomputable def nb057AlphaDummy231 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy221 f))).fv ∪
      ((Class.cv (nb057AlphaDummy221 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_232`. -/
@[expose]
noncomputable def nb057AlphaDummy232 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy202)
          (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
            (Wff.classEq (Class.cv (nb057AlphaDummy202))
              (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy202)
          (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
            (Wff.classEq (Class.cv (nb057AlphaDummy202))
              (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_233`. -/
@[expose]
noncomputable def nb057AlphaDummy233 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy204 f)
          (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy204 f)
          (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_234`. -/
@[expose]
noncomputable def nb057AlphaDummy234 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy203))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_235`. -/
@[expose]
noncomputable def nb057AlphaDummy235 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy205 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_236`. -/
@[expose]
noncomputable def nb057AlphaDummy236 : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy203)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy203)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_237`. -/
@[expose]
noncomputable def nb057AlphaDummy237 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy205 f)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy205 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_238`. -/
@[expose]
noncomputable def nb057AlphaDummy238 : Var :=
  (freshVar (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_239`. -/
@[expose]
noncomputable def nb057AlphaDummy239 : Var :=
  (freshVar (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_240`. -/
@[expose]
noncomputable def nb057AlphaDummy240 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_241`. -/
@[expose]
noncomputable def nb057AlphaDummy241 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_242`. -/
@[expose]
noncomputable def nb057AlphaDummy242 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_243`. -/
@[expose]
noncomputable def nb057AlphaDummy243 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_244`. -/
@[expose]
noncomputable def nb057AlphaDummy244 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy241 f))).fv ∪
      ((Class.cv (nb057AlphaDummy240 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_245`. -/
@[expose]
noncomputable def nb057AlphaDummy245 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy241 f))).fv ∪
      ((Class.cv (nb057AlphaDummy240 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_246`. -/
@[expose]
noncomputable def nb057AlphaDummy246 : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCphi (Class.cv (nb057AlphaDummy243)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_247`. -/
@[expose]
noncomputable def nb057AlphaDummy247 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCphi (Class.cv (nb057AlphaDummy245 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_248`. -/
@[expose]
noncomputable def nb057AlphaDummy248 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy242)
          (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
            (Wff.classEq (Class.cv (nb057AlphaDummy242))
              (synCphi (Class.cv (nb057AlphaDummy243))))))).fv ∪
      ((Class.cab (nb057AlphaDummy242)
          (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
            (Wff.classEq (Class.cv (nb057AlphaDummy242))
              (synCphi (Class.cv (nb057AlphaDummy243))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_249`. -/
@[expose]
noncomputable def nb057AlphaDummy249 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy244 f)
          (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
              (synCphi (Class.cv (nb057AlphaDummy245 f))))))).fv ∪
      ((Class.cab (nb057AlphaDummy244 f)
          (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
              (synCphi (Class.cv (nb057AlphaDummy245 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_250`. -/
@[expose]
noncomputable def nb057AlphaDummy250 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy243))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_251`. -/
@[expose]
noncomputable def nb057AlphaDummy251 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy243))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_252`. -/
@[expose]
noncomputable def nb057AlphaDummy252 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy245 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_253`. -/
@[expose]
noncomputable def nb057AlphaDummy253 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy245 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_254`. -/
@[expose]
noncomputable def nb057AlphaDummy254 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy250)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy250)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy250))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_255`. -/
@[expose]
noncomputable def nb057AlphaDummy255 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057AlphaDummy252 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb057AlphaDummy252 f)) (synC1c))).fv ∪
      ((Class.cv (nb057AlphaDummy252 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_256`. -/
@[expose]
noncomputable def nb057AlphaDummy256 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_257`. -/
@[expose]
noncomputable def nb057AlphaDummy257 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_258`. -/
@[expose]
noncomputable def nb057AlphaDummy258 : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_259`. -/
@[expose]
noncomputable def nb057AlphaDummy259 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_260`. -/
@[expose]
noncomputable def nb057AlphaDummy260 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_261`. -/
@[expose]
noncomputable def nb057AlphaDummy261 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_262`. -/
@[expose]
noncomputable def nb057AlphaDummy262 : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy257))
          (Class.cv (nb057AlphaDummy258)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_263`. -/
@[expose]
noncomputable def nb057AlphaDummy263 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb057AlphaDummy260 f))
          (Class.cv (nb057AlphaDummy261 f)))).fv ∪
      ((synCnin (Class.cv (nb057AlphaDummy260 f)) (Class.cv (nb057AlphaDummy261 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_264`. -/
@[expose]
noncomputable def nb057AlphaDummy264 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_265`. -/
@[expose]
noncomputable def nb057AlphaDummy265 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy260 f))).fv ∪
      ((Class.cv (nb057AlphaDummy261 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_266`. -/
@[expose]
noncomputable def nb057AlphaDummy266 : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy257)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy258)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_267`. -/
@[expose]
noncomputable def nb057AlphaDummy267 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb057AlphaDummy260 f)))).fv ∪
      ((synCcompl (Class.cv (nb057AlphaDummy261 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_268`. -/
@[expose]
noncomputable def nb057AlphaDummy268 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy257))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_269`. -/
@[expose]
noncomputable def nb057AlphaDummy269 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy260 f))).fv ∪
      ((Class.cv (nb057AlphaDummy260 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_270`. -/
@[expose]
noncomputable def nb057AlphaDummy270 : Var :=
  (freshVar
    (((Class.cv (nb057AlphaDummy258))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_271`. -/
@[expose]
noncomputable def nb057AlphaDummy271 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057AlphaDummy261 f))).fv ∪
      ((Class.cv (nb057AlphaDummy261 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_272`. -/
@[expose]
noncomputable def nb057AlphaDummy272 : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy242)
          (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
            (Wff.classEq (Class.cv (nb057AlphaDummy242))
              (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy242)
          (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
            (Wff.classEq (Class.cv (nb057AlphaDummy242))
              (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_273`. -/
@[expose]
noncomputable def nb057AlphaDummy273 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057AlphaDummy244 f)
          (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy244 f)
          (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
            (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
              (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_274`. -/
@[expose]
noncomputable def nb057AlphaDummy274 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy243))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_275`. -/
@[expose]
noncomputable def nb057AlphaDummy275 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb057AlphaDummy245 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_276`. -/
@[expose]
noncomputable def nb057AlphaDummy276 : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy243)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy243)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb057_alpha_dummy_277`. -/
@[expose]
noncomputable def nb057AlphaDummy277 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb057AlphaDummy245 f)))).fv ∪
      ((synCphi (Class.cv (nb057AlphaDummy245 f)))).fv) 0)

theorem nb057_fresh_000 :
    (nb057AlphaDummy034) ∉
      (((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy034] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_001 :
    (nb057AlphaDummy010) ∉
      (((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCphi (Class.cv (nb057AlphaDummy005))))))).fv ∪
        ((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCphi (Class.cv (nb057AlphaDummy005))))))).fv) :=
  by
  simpa only [nb057AlphaDummy010] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCphi (Class.cv (nb057AlphaDummy005))))))).fv ∪
        ((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCphi (Class.cv (nb057AlphaDummy005))))))).fv)
      0

theorem nb057_fresh_002 (f : Var) (a : Var) :
    (nb057AlphaDummy035 f a) ∉
      (((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_003 (f : Var) (a : Var) :
    (nb057AlphaDummy011 f a) ∉
      (((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCphi (Class.cv (nb057AlphaDummy007 f a))))))).fv ∪
        ((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCphi (Class.cv (nb057AlphaDummy007 f a))))))).fv) :=
  by
  simpa only [nb057AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCphi (Class.cv (nb057AlphaDummy007 f a))))))).fv ∪
        ((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCphi (Class.cv (nb057AlphaDummy007 f a))))))).fv)
      0

theorem nb057_fresh_004 :
    (nb057AlphaDummy058) ∉
      (((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCphi (Class.cv (nb057AlphaDummy053))))))).fv ∪
        ((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCphi (Class.cv (nb057AlphaDummy053))))))).fv) :=
  by
  simpa only [nb057AlphaDummy058] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCphi (Class.cv (nb057AlphaDummy053))))))).fv ∪
        ((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCphi (Class.cv (nb057AlphaDummy053))))))).fv)
      0

theorem nb057_fresh_005 :
    (nb057AlphaDummy082) ∉
      (((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy082] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_006 (f : Var) :
    (nb057AlphaDummy059 f) ∉
      (((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCphi (Class.cv (nb057AlphaDummy055 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCphi (Class.cv (nb057AlphaDummy055 f))))))).fv) :=
  by
  simpa only [nb057AlphaDummy059] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCphi (Class.cv (nb057AlphaDummy055 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCphi (Class.cv (nb057AlphaDummy055 f))))))).fv)
      0

theorem nb057_fresh_007 (f : Var) :
    (nb057AlphaDummy083 f) ∉
      (((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy083] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_008 :
    (nb057AlphaDummy094) ∉
      (((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCphi (Class.cv (nb057AlphaDummy089))))))).fv ∪
        ((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCphi (Class.cv (nb057AlphaDummy089))))))).fv) :=
  by
  simpa only [nb057AlphaDummy094] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCphi (Class.cv (nb057AlphaDummy089))))))).fv ∪
        ((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCphi (Class.cv (nb057AlphaDummy089))))))).fv)
      0

theorem nb057_fresh_009 :
    (nb057AlphaDummy118) ∉
      (((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy118] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_010 (f : Var) :
    (nb057AlphaDummy095 f) ∉
      (((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCphi (Class.cv (nb057AlphaDummy091 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCphi (Class.cv (nb057AlphaDummy091 f))))))).fv) :=
  by
  simpa only [nb057AlphaDummy095] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCphi (Class.cv (nb057AlphaDummy091 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCphi (Class.cv (nb057AlphaDummy091 f))))))).fv)
      0

theorem nb057_fresh_011 (f : Var) :
    (nb057AlphaDummy119 f) ∉
      (((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy119] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_012 :
    (nb057AlphaDummy136) ∉
      (((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCphi (Class.cv (nb057AlphaDummy131))))))).fv ∪
        ((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCphi (Class.cv (nb057AlphaDummy131))))))).fv) :=
  by
  simpa only [nb057AlphaDummy136] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCphi (Class.cv (nb057AlphaDummy131))))))).fv ∪
        ((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCphi (Class.cv (nb057AlphaDummy131))))))).fv)
      0

theorem nb057_fresh_013 :
    (nb057AlphaDummy160) ∉
      (((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy160] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_014 (f : Var) :
    (nb057AlphaDummy137 f) ∉
      (((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCphi (Class.cv (nb057AlphaDummy133 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCphi (Class.cv (nb057AlphaDummy133 f))))))).fv) :=
  by
  simpa only [nb057AlphaDummy137] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCphi (Class.cv (nb057AlphaDummy133 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCphi (Class.cv (nb057AlphaDummy133 f))))))).fv)
      0

theorem nb057_fresh_015 (f : Var) :
    (nb057AlphaDummy161 f) ∉
      (((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy161] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_016 :
    (nb057AlphaDummy196) ∉
      (((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy196] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_017 :
    (nb057AlphaDummy172) ∉
      (((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCphi (Class.cv (nb057AlphaDummy167))))))).fv ∪
        ((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCphi (Class.cv (nb057AlphaDummy167))))))).fv) :=
  by
  simpa only [nb057AlphaDummy172] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCphi (Class.cv (nb057AlphaDummy167))))))).fv ∪
        ((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCphi (Class.cv (nb057AlphaDummy167))))))).fv)
      0

theorem nb057_fresh_018 (f : Var) :
    (nb057AlphaDummy197 f) ∉
      (((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy197] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_019 (f : Var) :
    (nb057AlphaDummy173 f) ∉
      (((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCphi (Class.cv (nb057AlphaDummy169 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCphi (Class.cv (nb057AlphaDummy169 f))))))).fv) :=
  by
  simpa only [nb057AlphaDummy173] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCphi (Class.cv (nb057AlphaDummy169 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCphi (Class.cv (nb057AlphaDummy169 f))))))).fv)
      0

theorem nb057_fresh_020 :
    (nb057AlphaDummy232) ∉
      (((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy232] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_021 :
    (nb057AlphaDummy208) ∉
      (((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCphi (Class.cv (nb057AlphaDummy203))))))).fv ∪
        ((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCphi (Class.cv (nb057AlphaDummy203))))))).fv) :=
  by
  simpa only [nb057AlphaDummy208] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCphi (Class.cv (nb057AlphaDummy203))))))).fv ∪
        ((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCphi (Class.cv (nb057AlphaDummy203))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part003`. -/


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

theorem nb057_fresh_022 (f : Var) :
    (nb057AlphaDummy233 f) ∉
      (((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy233] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_023 (f : Var) :
    (nb057AlphaDummy209 f) ∉
      (((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCphi (Class.cv (nb057AlphaDummy205 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCphi (Class.cv (nb057AlphaDummy205 f))))))).fv) :=
  by
  simpa only [nb057AlphaDummy209] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCphi (Class.cv (nb057AlphaDummy205 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCphi (Class.cv (nb057AlphaDummy205 f))))))).fv)
      0

theorem nb057_fresh_024 :
    (nb057AlphaDummy272) ∉
      (((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy272] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_025 :
    (nb057AlphaDummy248) ∉
      (((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCphi (Class.cv (nb057AlphaDummy243))))))).fv ∪
        ((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCphi (Class.cv (nb057AlphaDummy243))))))).fv) :=
  by
  simpa only [nb057AlphaDummy248] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCphi (Class.cv (nb057AlphaDummy243))))))).fv ∪
        ((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCphi (Class.cv (nb057AlphaDummy243))))))).fv)
      0

theorem nb057_fresh_026 (f : Var) :
    (nb057AlphaDummy273 f) ∉
      (((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb057AlphaDummy273] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb057_fresh_027 (f : Var) :
    (nb057AlphaDummy249 f) ∉
      (((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCphi (Class.cv (nb057AlphaDummy245 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCphi (Class.cv (nb057AlphaDummy245 f))))))).fv) :=
  by
  simpa only [nb057AlphaDummy249] using
    freshVar_not_mem
      (((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCphi (Class.cv (nb057AlphaDummy245 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCphi (Class.cv (nb057AlphaDummy245 f))))))).fv)
      0

theorem nb057_fresh_028 :
    (nb057AlphaDummy124) ∉ (((Class.cv (nb057AlphaDummy001))).fv) := by
  simpa only [nb057AlphaDummy124] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy001))).fv) 0

theorem nb057_fresh_029 :
    (nb057AlphaDummy125) ∉ (((Class.cv (nb057AlphaDummy001))).fv) := by
  simpa only [nb057AlphaDummy125] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy001))).fv) 1

theorem nb057_distinct_030 : (nb057AlphaDummy124) ≠ (nb057AlphaDummy125) := by
  simpa only [nb057AlphaDummy124, nb057AlphaDummy125] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_031 :
    (nb057AlphaDummy004) ∉
      (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv) :=
  by
  simpa only [nb057AlphaDummy004] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv)
      0

theorem nb057_fresh_032 :
    (nb057AlphaDummy005) ∉
      (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv) :=
  by
  simpa only [nb057AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv)
      1

theorem nb057_distinct_033 : (nb057AlphaDummy004) ≠ (nb057AlphaDummy005) := by
  simpa only [nb057AlphaDummy004, nb057AlphaDummy005] using
    (freshVar_injective
      (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_034 :
    (nb057AlphaDummy044) ∉
      (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) :=
  by
  simpa only [nb057AlphaDummy044] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv)
      0

theorem nb057_fresh_035 :
    (nb057AlphaDummy045) ∉
      (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) :=
  by
  simpa only [nb057AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv)
      1

theorem nb057_fresh_036 :
    (nb057AlphaDummy046) ∉
      (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) :=
  by
  simpa only [nb057AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv)
      2

theorem nb057_distinct_037 : (nb057AlphaDummy044) ≠ (nb057AlphaDummy045) := by
  simpa only [nb057AlphaDummy044, nb057AlphaDummy045] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_038 : (nb057AlphaDummy044) ≠ (nb057AlphaDummy046) := by
  simpa only [nb057AlphaDummy044, nb057AlphaDummy046] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_039 : (nb057AlphaDummy045) ≠ (nb057AlphaDummy046) := by
  simpa only [nb057AlphaDummy045, nb057AlphaDummy046] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_040 :
    (nb057AlphaDummy012) ∉ (((Class.cv (nb057AlphaDummy005))).fv) := by
  simpa only [nb057AlphaDummy012] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy005))).fv) 0

theorem nb057_fresh_041 :
    (nb057AlphaDummy013) ∉ (((Class.cv (nb057AlphaDummy005))).fv) := by
  simpa only [nb057AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy005))).fv) 1

theorem nb057_distinct_042 : (nb057AlphaDummy012) ≠ (nb057AlphaDummy013) := by
  simpa only [nb057AlphaDummy012, nb057AlphaDummy013] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy005))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_043 (f : Var) (a : Var) :
    (nb057AlphaDummy014 f a) ∉ (((Class.cv (nb057AlphaDummy007 f a))).fv) := by
  simpa only [nb057AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy007 f a))).fv) 0

theorem nb057_fresh_044 (f : Var) (a : Var) :
    (nb057AlphaDummy015 f a) ∉ (((Class.cv (nb057AlphaDummy007 f a))).fv) := by
  simpa only [nb057AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy007 f a))).fv) 1

theorem nb057_distinct_045 (f : Var) (a : Var) :
    (nb057AlphaDummy014 f a) ≠ (nb057AlphaDummy015 f a) := by
  simpa only [nb057AlphaDummy014, nb057AlphaDummy015] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy007 f a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_046 :
    (nb057AlphaDummy018) ∉
      (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_047 :
    (nb057AlphaDummy019) ∉
      (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_048 :
    (nb057AlphaDummy020) ∉
      (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_049 : (nb057AlphaDummy018) ≠ (nb057AlphaDummy019) := by
  simpa only [nb057AlphaDummy018, nb057AlphaDummy019] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_050 : (nb057AlphaDummy018) ≠ (nb057AlphaDummy020) := by
  simpa only [nb057AlphaDummy018, nb057AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_051 : (nb057AlphaDummy019) ≠ (nb057AlphaDummy020) := by
  simpa only [nb057AlphaDummy019, nb057AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_052 (f : Var) (a : Var) :
    (nb057AlphaDummy021 f a) ∉
      (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_053 (f : Var) (a : Var) :
    (nb057AlphaDummy022 f a) ∉
      (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_054 (f : Var) (a : Var) :
    (nb057AlphaDummy023 f a) ∉
      (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_055 (f : Var) (a : Var) :
    (nb057AlphaDummy021 f a) ≠ (nb057AlphaDummy022 f a) := by
  simpa only [nb057AlphaDummy021, nb057AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_distinct_056 (f : Var) (a : Var) :
    (nb057AlphaDummy021 f a) ≠ (nb057AlphaDummy023 f a) := by
  simpa only [nb057AlphaDummy021, nb057AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb057_distinct_057 (f : Var) (a : Var) :
    (nb057AlphaDummy022 f a) ≠ (nb057AlphaDummy023 f a) := by
  simpa only [nb057AlphaDummy022, nb057AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb057_fresh_058 :
    (nb057AlphaDummy030) ∉
      (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy019))).fv) :=
  by
  simpa only [nb057AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy019))).fv)
      0

theorem nb057_fresh_059 :
    (nb057AlphaDummy026) ∉
      (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv) :=
  by
  simpa only [nb057AlphaDummy026] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv)
      0

theorem nb057_fresh_060 :
    (nb057AlphaDummy032) ∉
      (((Class.cv (nb057AlphaDummy020))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv) :=
  by
  simpa only [nb057AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy020))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv)
      0

theorem nb057_fresh_061 (f : Var) (a : Var) :
    (nb057AlphaDummy031 f a) ∉
      (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy022 f a))).fv) :=
  by
  simpa only [nb057AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy022 f a))).fv)
      0

theorem nb057_fresh_062 (f : Var) (a : Var) :
    (nb057AlphaDummy027 f a) ∉
      (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy023 f a))).fv) :=
  by
  simpa only [nb057AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy023 f a))).fv)
      0

theorem nb057_fresh_063 (f : Var) (a : Var) :
    (nb057AlphaDummy033 f a) ∉
      (((Class.cv (nb057AlphaDummy023 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy023 f a))).fv) :=
  by
  simpa only [nb057AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy023 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy023 f a))).fv)
      0

theorem nb057_fresh_064 :
    (nb057AlphaDummy052) ∉
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) :=
  by
  simpa only [nb057AlphaDummy052] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv)
      0

theorem nb057_fresh_065 :
    (nb057AlphaDummy053) ∉
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) :=
  by
  simpa only [nb057AlphaDummy053] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv)
      1

theorem nb057_distinct_066 : (nb057AlphaDummy052) ≠ (nb057AlphaDummy053) := by
  simpa only [nb057AlphaDummy052, nb057AlphaDummy053] using
    (freshVar_injective
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_067 :
    (nb057AlphaDummy088) ∉
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv) :=
  by
  simpa only [nb057AlphaDummy088] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv)
      0

theorem nb057_fresh_068 :
    (nb057AlphaDummy089) ∉
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv) :=
  by
  simpa only [nb057AlphaDummy089] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv)
      1

theorem nb057_distinct_069 : (nb057AlphaDummy088) ≠ (nb057AlphaDummy089) := by
  simpa only [nb057AlphaDummy088, nb057AlphaDummy089] using
    (freshVar_injective
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_070 :
    (nb057AlphaDummy202) ∉
      (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) :=
  by
  simpa only [nb057AlphaDummy202] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv)
      0

theorem nb057_fresh_071 :
    (nb057AlphaDummy203) ∉
      (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) :=
  by
  simpa only [nb057AlphaDummy203] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv)
      1

theorem nb057_distinct_072 : (nb057AlphaDummy202) ≠ (nb057AlphaDummy203) := by
  simpa only [nb057AlphaDummy202, nb057AlphaDummy203] using
    (freshVar_injective
      (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_073 (f : Var) :
    (nb057AlphaDummy054 f) ∉
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv) :=
  by
  simpa only [nb057AlphaDummy054] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv)
      0

theorem nb057_fresh_074 (f : Var) :
    (nb057AlphaDummy055 f) ∉
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv) :=
  by
  simpa only [nb057AlphaDummy055] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv)
      1

theorem nb057_distinct_075 (f : Var) :
    (nb057AlphaDummy054 f) ≠ (nb057AlphaDummy055 f) := by
  simpa only [nb057AlphaDummy054, nb057AlphaDummy055] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy047 f))).fv ∪
        ((Class.cv (nb057AlphaDummy048 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_076 (f : Var) :
    (nb057AlphaDummy090 f) ∉
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy049 f))).fv) :=
  by
  simpa only [nb057AlphaDummy090] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy049 f))).fv)
      0

theorem nb057_fresh_077 (f : Var) :
    (nb057AlphaDummy091 f) ∉
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy049 f))).fv) :=
  by
  simpa only [nb057AlphaDummy091] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy049 f))).fv)
      1

theorem nb057_distinct_078 (f : Var) :
    (nb057AlphaDummy090 f) ≠ (nb057AlphaDummy091 f) := by
  simpa only [nb057AlphaDummy090, nb057AlphaDummy091] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy047 f))).fv ∪
        ((Class.cv (nb057AlphaDummy049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_079 (f : Var) :
    (nb057AlphaDummy204 f) ∉
      (((Class.cv (nb057AlphaDummy049 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv) :=
  by
  simpa only [nb057AlphaDummy204] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy049 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv)
      0

theorem nb057_fresh_080 (f : Var) :
    (nb057AlphaDummy205 f) ∉
      (((Class.cv (nb057AlphaDummy049 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv) :=
  by
  simpa only [nb057AlphaDummy205] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy049 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv)
      1

theorem nb057_distinct_081 (f : Var) :
    (nb057AlphaDummy204 f) ≠ (nb057AlphaDummy205 f) := by
  simpa only [nb057AlphaDummy204, nb057AlphaDummy205] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy049 f))).fv ∪
        ((Class.cv (nb057AlphaDummy048 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_082 :
    (nb057AlphaDummy060) ∉ (((Class.cv (nb057AlphaDummy053))).fv) := by
  simpa only [nb057AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy053))).fv) 0

theorem nb057_fresh_083 :
    (nb057AlphaDummy061) ∉ (((Class.cv (nb057AlphaDummy053))).fv) := by
  simpa only [nb057AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy053))).fv) 1

theorem nb057_distinct_084 : (nb057AlphaDummy060) ≠ (nb057AlphaDummy061) := by
  simpa only [nb057AlphaDummy060, nb057AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy053))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_085 (f : Var) :
    (nb057AlphaDummy062 f) ∉ (((Class.cv (nb057AlphaDummy055 f))).fv) := by
  simpa only [nb057AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy055 f))).fv) 0

theorem nb057_fresh_086 (f : Var) :
    (nb057AlphaDummy063 f) ∉ (((Class.cv (nb057AlphaDummy055 f))).fv) := by
  simpa only [nb057AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy055 f))).fv) 1

theorem nb057_distinct_087 (f : Var) :
    (nb057AlphaDummy062 f) ≠ (nb057AlphaDummy063 f) := by
  simpa only [nb057AlphaDummy062, nb057AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy055 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_088 :
    (nb057AlphaDummy066) ∉
      (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy066] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_089 :
    (nb057AlphaDummy067) ∉
      (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy067] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_090 :
    (nb057AlphaDummy068) ∉
      (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy068] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_091 : (nb057AlphaDummy066) ≠ (nb057AlphaDummy067) := by
  simpa only [nb057AlphaDummy066, nb057AlphaDummy067] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_092 : (nb057AlphaDummy066) ≠ (nb057AlphaDummy068) := by
  simpa only [nb057AlphaDummy066, nb057AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_093 : (nb057AlphaDummy067) ≠ (nb057AlphaDummy068) := by
  simpa only [nb057AlphaDummy067, nb057AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_094 (f : Var) :
    (nb057AlphaDummy069 f) ∉
      (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy069] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_095 (f : Var) :
    (nb057AlphaDummy070 f) ∉
      (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy070] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_096 (f : Var) :
    (nb057AlphaDummy071 f) ∉
      (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy071] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_097 (f : Var) :
    (nb057AlphaDummy069 f) ≠ (nb057AlphaDummy070 f) := by
  simpa only [nb057AlphaDummy069, nb057AlphaDummy070] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_098 (f : Var) :
    (nb057AlphaDummy069 f) ≠ (nb057AlphaDummy071 f) := by
  simpa only [nb057AlphaDummy069, nb057AlphaDummy071] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_099 (f : Var) :
    (nb057AlphaDummy070 f) ≠ (nb057AlphaDummy071 f) := by
  simpa only [nb057AlphaDummy070, nb057AlphaDummy071] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_100 :
    (nb057AlphaDummy078) ∉
      (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy067))).fv) :=
  by
  simpa only [nb057AlphaDummy078] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy067))).fv)
      0

theorem nb057_fresh_101 :
    (nb057AlphaDummy074) ∉
      (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv) :=
  by
  simpa only [nb057AlphaDummy074] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv)
      0

theorem nb057_fresh_102 :
    (nb057AlphaDummy080) ∉
      (((Class.cv (nb057AlphaDummy068))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv) :=
  by
  simpa only [nb057AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy068))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv)
      0

theorem nb057_fresh_103 (f : Var) :
    (nb057AlphaDummy079 f) ∉
      (((Class.cv (nb057AlphaDummy070 f))).fv ∪ ((Class.cv (nb057AlphaDummy070 f))).fv) :=
  by
  simpa only [nb057AlphaDummy079] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy070 f))).fv ∪ ((Class.cv (nb057AlphaDummy070 f))).fv)
      0

theorem nb057_fresh_104 (f : Var) :
    (nb057AlphaDummy075 f) ∉
      (((Class.cv (nb057AlphaDummy070 f))).fv ∪ ((Class.cv (nb057AlphaDummy071 f))).fv) :=
  by
  simpa only [nb057AlphaDummy075] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy070 f))).fv ∪ ((Class.cv (nb057AlphaDummy071 f))).fv)
      0

theorem nb057_fresh_105 (f : Var) :
    (nb057AlphaDummy081 f) ∉
      (((Class.cv (nb057AlphaDummy071 f))).fv ∪ ((Class.cv (nb057AlphaDummy071 f))).fv) :=
  by
  simpa only [nb057AlphaDummy081] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy071 f))).fv ∪ ((Class.cv (nb057AlphaDummy071 f))).fv)
      0

theorem nb057_fresh_106 :
    (nb057AlphaDummy096) ∉ (((Class.cv (nb057AlphaDummy089))).fv) := by
  simpa only [nb057AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy089))).fv) 0

theorem nb057_fresh_107 :
    (nb057AlphaDummy097) ∉ (((Class.cv (nb057AlphaDummy089))).fv) := by
  simpa only [nb057AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy089))).fv) 1

theorem nb057_distinct_108 : (nb057AlphaDummy096) ≠ (nb057AlphaDummy097) := by
  simpa only [nb057AlphaDummy096, nb057AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy089))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_109 (f : Var) :
    (nb057AlphaDummy098 f) ∉ (((Class.cv (nb057AlphaDummy091 f))).fv) := by
  simpa only [nb057AlphaDummy098] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy091 f))).fv) 0

theorem nb057_fresh_110 (f : Var) :
    (nb057AlphaDummy099 f) ∉ (((Class.cv (nb057AlphaDummy091 f))).fv) := by
  simpa only [nb057AlphaDummy099] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy091 f))).fv) 1

theorem nb057_distinct_111 (f : Var) :
    (nb057AlphaDummy098 f) ≠ (nb057AlphaDummy099 f) := by
  simpa only [nb057AlphaDummy098, nb057AlphaDummy099] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy091 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_112 :
    (nb057AlphaDummy102) ∉
      (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy102] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_113 :
    (nb057AlphaDummy103) ∉
      (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy103] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_114 :
    (nb057AlphaDummy104) ∉
      (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy104] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_115 : (nb057AlphaDummy102) ≠ (nb057AlphaDummy103) := by
  simpa only [nb057AlphaDummy102, nb057AlphaDummy103] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_116 : (nb057AlphaDummy102) ≠ (nb057AlphaDummy104) := by
  simpa only [nb057AlphaDummy102, nb057AlphaDummy104] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_117 : (nb057AlphaDummy103) ≠ (nb057AlphaDummy104) := by
  simpa only [nb057AlphaDummy103, nb057AlphaDummy104] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_118 (f : Var) :
    (nb057AlphaDummy105 f) ∉
      (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy105] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_119 (f : Var) :
    (nb057AlphaDummy106 f) ∉
      (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy106] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_120 (f : Var) :
    (nb057AlphaDummy107 f) ∉
      (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy107] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_121 (f : Var) :
    (nb057AlphaDummy105 f) ≠ (nb057AlphaDummy106 f) := by
  simpa only [nb057AlphaDummy105, nb057AlphaDummy106] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_122 (f : Var) :
    (nb057AlphaDummy105 f) ≠ (nb057AlphaDummy107 f) := by
  simpa only [nb057AlphaDummy105, nb057AlphaDummy107] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_123 (f : Var) :
    (nb057AlphaDummy106 f) ≠ (nb057AlphaDummy107 f) := by
  simpa only [nb057AlphaDummy106, nb057AlphaDummy107] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_124 :
    (nb057AlphaDummy114) ∉
      (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy103))).fv) :=
  by
  simpa only [nb057AlphaDummy114] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy103))).fv)
      0

theorem nb057_fresh_125 :
    (nb057AlphaDummy110) ∉
      (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv) :=
  by
  simpa only [nb057AlphaDummy110] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv)
      0

theorem nb057_fresh_126 :
    (nb057AlphaDummy116) ∉
      (((Class.cv (nb057AlphaDummy104))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv) :=
  by
  simpa only [nb057AlphaDummy116] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy104))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv)
      0

theorem nb057_fresh_127 (f : Var) :
    (nb057AlphaDummy115 f) ∉
      (((Class.cv (nb057AlphaDummy106 f))).fv ∪ ((Class.cv (nb057AlphaDummy106 f))).fv) :=
  by
  simpa only [nb057AlphaDummy115] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy106 f))).fv ∪ ((Class.cv (nb057AlphaDummy106 f))).fv)
      0

theorem nb057_fresh_128 (f : Var) :
    (nb057AlphaDummy111 f) ∉
      (((Class.cv (nb057AlphaDummy106 f))).fv ∪ ((Class.cv (nb057AlphaDummy107 f))).fv) :=
  by
  simpa only [nb057AlphaDummy111] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy106 f))).fv ∪ ((Class.cv (nb057AlphaDummy107 f))).fv)
      0

theorem nb057_fresh_129 (f : Var) :
    (nb057AlphaDummy117 f) ∉
      (((Class.cv (nb057AlphaDummy107 f))).fv ∪ ((Class.cv (nb057AlphaDummy107 f))).fv) :=
  by
  simpa only [nb057AlphaDummy117] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy107 f))).fv ∪ ((Class.cv (nb057AlphaDummy107 f))).fv)
      0

theorem nb057_fresh_130 :
    (nb057AlphaDummy130) ∉
      (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv) :=
  by
  simpa only [nb057AlphaDummy130] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv)
      0

theorem nb057_fresh_131 :
    (nb057AlphaDummy131) ∉
      (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv) :=
  by
  simpa only [nb057AlphaDummy131] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv)
      1

theorem nb057_distinct_132 : (nb057AlphaDummy130) ≠ (nb057AlphaDummy131) := by
  simpa only [nb057AlphaDummy130, nb057AlphaDummy131] using
    (freshVar_injective
      (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_133 :
    (nb057AlphaDummy166) ∉
      (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv) :=
  by
  simpa only [nb057AlphaDummy166] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv)
      0

theorem nb057_fresh_134 :
    (nb057AlphaDummy167) ∉
      (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv) :=
  by
  simpa only [nb057AlphaDummy167] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv)
      1

theorem nb057_distinct_135 : (nb057AlphaDummy166) ≠ (nb057AlphaDummy167) := by
  simpa only [nb057AlphaDummy166, nb057AlphaDummy167] using
    (freshVar_injective
      (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_136 (f : Var) :
    (nb057AlphaDummy132 f) ∉
      (((Class.cv (nb057AlphaDummy126 f))).fv ∪ ((Class.cv (nb057AlphaDummy127 f))).fv) :=
  by
  simpa only [nb057AlphaDummy132] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy126 f))).fv ∪ ((Class.cv (nb057AlphaDummy127 f))).fv)
      0

theorem nb057_fresh_137 (f : Var) :
    (nb057AlphaDummy133 f) ∉
      (((Class.cv (nb057AlphaDummy126 f))).fv ∪ ((Class.cv (nb057AlphaDummy127 f))).fv) :=
  by
  simpa only [nb057AlphaDummy133] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy126 f))).fv ∪ ((Class.cv (nb057AlphaDummy127 f))).fv)
      1

theorem nb057_distinct_138 (f : Var) :
    (nb057AlphaDummy132 f) ≠ (nb057AlphaDummy133 f) := by
  simpa only [nb057AlphaDummy132, nb057AlphaDummy133] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy126 f))).fv ∪
        ((Class.cv (nb057AlphaDummy127 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_139 (f : Var) :
    (nb057AlphaDummy168 f) ∉
      (((Class.cv (nb057AlphaDummy127 f))).fv ∪ ((Class.cv (nb057AlphaDummy126 f))).fv) :=
  by
  simpa only [nb057AlphaDummy168] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy127 f))).fv ∪ ((Class.cv (nb057AlphaDummy126 f))).fv)
      0

theorem nb057_fresh_140 (f : Var) :
    (nb057AlphaDummy169 f) ∉
      (((Class.cv (nb057AlphaDummy127 f))).fv ∪ ((Class.cv (nb057AlphaDummy126 f))).fv) :=
  by
  simpa only [nb057AlphaDummy169] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy127 f))).fv ∪ ((Class.cv (nb057AlphaDummy126 f))).fv)
      1

theorem nb057_distinct_141 (f : Var) :
    (nb057AlphaDummy168 f) ≠ (nb057AlphaDummy169 f) := by
  simpa only [nb057AlphaDummy168, nb057AlphaDummy169] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy127 f))).fv ∪
        ((Class.cv (nb057AlphaDummy126 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_142 :
    (nb057AlphaDummy138) ∉ (((Class.cv (nb057AlphaDummy131))).fv) := by
  simpa only [nb057AlphaDummy138] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy131))).fv) 0

theorem nb057_fresh_143 :
    (nb057AlphaDummy139) ∉ (((Class.cv (nb057AlphaDummy131))).fv) := by
  simpa only [nb057AlphaDummy139] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy131))).fv) 1

theorem nb057_distinct_144 : (nb057AlphaDummy138) ≠ (nb057AlphaDummy139) := by
  simpa only [nb057AlphaDummy138, nb057AlphaDummy139] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy131))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_145 (f : Var) :
    (nb057AlphaDummy140 f) ∉ (((Class.cv (nb057AlphaDummy133 f))).fv) := by
  simpa only [nb057AlphaDummy140] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy133 f))).fv) 0

theorem nb057_fresh_146 (f : Var) :
    (nb057AlphaDummy141 f) ∉ (((Class.cv (nb057AlphaDummy133 f))).fv) := by
  simpa only [nb057AlphaDummy141] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy133 f))).fv) 1

theorem nb057_distinct_147 (f : Var) :
    (nb057AlphaDummy140 f) ≠ (nb057AlphaDummy141 f) := by
  simpa only [nb057AlphaDummy140, nb057AlphaDummy141] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy133 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_148 :
    (nb057AlphaDummy144) ∉
      (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy144] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_149 :
    (nb057AlphaDummy145) ∉
      (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy145] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_150 :
    (nb057AlphaDummy146) ∉
      (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy146] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_151 : (nb057AlphaDummy144) ≠ (nb057AlphaDummy145) := by
  simpa only [nb057AlphaDummy144, nb057AlphaDummy145] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_152 : (nb057AlphaDummy144) ≠ (nb057AlphaDummy146) := by
  simpa only [nb057AlphaDummy144, nb057AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_153 : (nb057AlphaDummy145) ≠ (nb057AlphaDummy146) := by
  simpa only [nb057AlphaDummy145, nb057AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_154 (f : Var) :
    (nb057AlphaDummy147 f) ∉
      (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy147] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_155 (f : Var) :
    (nb057AlphaDummy148 f) ∉
      (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy148] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_156 (f : Var) :
    (nb057AlphaDummy149 f) ∉
      (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy149] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_157 (f : Var) :
    (nb057AlphaDummy147 f) ≠ (nb057AlphaDummy148 f) := by
  simpa only [nb057AlphaDummy147, nb057AlphaDummy148] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_158 (f : Var) :
    (nb057AlphaDummy147 f) ≠ (nb057AlphaDummy149 f) := by
  simpa only [nb057AlphaDummy147, nb057AlphaDummy149] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_159 (f : Var) :
    (nb057AlphaDummy148 f) ≠ (nb057AlphaDummy149 f) := by
  simpa only [nb057AlphaDummy148, nb057AlphaDummy149] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_160 :
    (nb057AlphaDummy156) ∉
      (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy145))).fv) :=
  by
  simpa only [nb057AlphaDummy156] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy145))).fv)
      0

theorem nb057_fresh_161 :
    (nb057AlphaDummy152) ∉
      (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv) :=
  by
  simpa only [nb057AlphaDummy152] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv)
      0

theorem nb057_fresh_162 :
    (nb057AlphaDummy158) ∉
      (((Class.cv (nb057AlphaDummy146))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv) :=
  by
  simpa only [nb057AlphaDummy158] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy146))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv)
      0

theorem nb057_fresh_163 (f : Var) :
    (nb057AlphaDummy157 f) ∉
      (((Class.cv (nb057AlphaDummy148 f))).fv ∪ ((Class.cv (nb057AlphaDummy148 f))).fv) :=
  by
  simpa only [nb057AlphaDummy157] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy148 f))).fv ∪ ((Class.cv (nb057AlphaDummy148 f))).fv)
      0

theorem nb057_fresh_164 (f : Var) :
    (nb057AlphaDummy153 f) ∉
      (((Class.cv (nb057AlphaDummy148 f))).fv ∪ ((Class.cv (nb057AlphaDummy149 f))).fv) :=
  by
  simpa only [nb057AlphaDummy153] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy148 f))).fv ∪ ((Class.cv (nb057AlphaDummy149 f))).fv)
      0

theorem nb057_fresh_165 (f : Var) :
    (nb057AlphaDummy159 f) ∉
      (((Class.cv (nb057AlphaDummy149 f))).fv ∪ ((Class.cv (nb057AlphaDummy149 f))).fv) :=
  by
  simpa only [nb057AlphaDummy159] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy149 f))).fv ∪ ((Class.cv (nb057AlphaDummy149 f))).fv)
      0

theorem nb057_fresh_166 :
    (nb057AlphaDummy174) ∉ (((Class.cv (nb057AlphaDummy167))).fv) := by
  simpa only [nb057AlphaDummy174] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy167))).fv) 0

theorem nb057_fresh_167 :
    (nb057AlphaDummy175) ∉ (((Class.cv (nb057AlphaDummy167))).fv) := by
  simpa only [nb057AlphaDummy175] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy167))).fv) 1

theorem nb057_distinct_168 : (nb057AlphaDummy174) ≠ (nb057AlphaDummy175) := by
  simpa only [nb057AlphaDummy174, nb057AlphaDummy175] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy167))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_169 (f : Var) :
    (nb057AlphaDummy176 f) ∉ (((Class.cv (nb057AlphaDummy169 f))).fv) := by
  simpa only [nb057AlphaDummy176] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy169 f))).fv) 0

theorem nb057_fresh_170 (f : Var) :
    (nb057AlphaDummy177 f) ∉ (((Class.cv (nb057AlphaDummy169 f))).fv) := by
  simpa only [nb057AlphaDummy177] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy169 f))).fv) 1

theorem nb057_distinct_171 (f : Var) :
    (nb057AlphaDummy176 f) ≠ (nb057AlphaDummy177 f) := by
  simpa only [nb057AlphaDummy176, nb057AlphaDummy177] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy169 f))).fv) (i := 0) (j := 1)
      (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part004`. -/


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

theorem nb057_fresh_172 :
    (nb057AlphaDummy180) ∉
      (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy180] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_173 :
    (nb057AlphaDummy181) ∉
      (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy181] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_174 :
    (nb057AlphaDummy182) ∉
      (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy182] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_175 : (nb057AlphaDummy180) ≠ (nb057AlphaDummy181) := by
  simpa only [nb057AlphaDummy180, nb057AlphaDummy181] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_176 : (nb057AlphaDummy180) ≠ (nb057AlphaDummy182) := by
  simpa only [nb057AlphaDummy180, nb057AlphaDummy182] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_177 : (nb057AlphaDummy181) ≠ (nb057AlphaDummy182) := by
  simpa only [nb057AlphaDummy181, nb057AlphaDummy182] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_178 (f : Var) :
    (nb057AlphaDummy183 f) ∉
      (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy183] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_179 (f : Var) :
    (nb057AlphaDummy184 f) ∉
      (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy184] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_180 (f : Var) :
    (nb057AlphaDummy185 f) ∉
      (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy185] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_181 (f : Var) :
    (nb057AlphaDummy183 f) ≠ (nb057AlphaDummy184 f) := by
  simpa only [nb057AlphaDummy183, nb057AlphaDummy184] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_182 (f : Var) :
    (nb057AlphaDummy183 f) ≠ (nb057AlphaDummy185 f) := by
  simpa only [nb057AlphaDummy183, nb057AlphaDummy185] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_183 (f : Var) :
    (nb057AlphaDummy184 f) ≠ (nb057AlphaDummy185 f) := by
  simpa only [nb057AlphaDummy184, nb057AlphaDummy185] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_184 :
    (nb057AlphaDummy192) ∉
      (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy181))).fv) :=
  by
  simpa only [nb057AlphaDummy192] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy181))).fv)
      0

theorem nb057_fresh_185 :
    (nb057AlphaDummy188) ∉
      (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv) :=
  by
  simpa only [nb057AlphaDummy188] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv)
      0

theorem nb057_fresh_186 :
    (nb057AlphaDummy194) ∉
      (((Class.cv (nb057AlphaDummy182))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv) :=
  by
  simpa only [nb057AlphaDummy194] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy182))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv)
      0

theorem nb057_fresh_187 (f : Var) :
    (nb057AlphaDummy193 f) ∉
      (((Class.cv (nb057AlphaDummy184 f))).fv ∪ ((Class.cv (nb057AlphaDummy184 f))).fv) :=
  by
  simpa only [nb057AlphaDummy193] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy184 f))).fv ∪ ((Class.cv (nb057AlphaDummy184 f))).fv)
      0

theorem nb057_fresh_188 (f : Var) :
    (nb057AlphaDummy189 f) ∉
      (((Class.cv (nb057AlphaDummy184 f))).fv ∪ ((Class.cv (nb057AlphaDummy185 f))).fv) :=
  by
  simpa only [nb057AlphaDummy189] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy184 f))).fv ∪ ((Class.cv (nb057AlphaDummy185 f))).fv)
      0

theorem nb057_fresh_189 (f : Var) :
    (nb057AlphaDummy195 f) ∉
      (((Class.cv (nb057AlphaDummy185 f))).fv ∪ ((Class.cv (nb057AlphaDummy185 f))).fv) :=
  by
  simpa only [nb057AlphaDummy195] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy185 f))).fv ∪ ((Class.cv (nb057AlphaDummy185 f))).fv)
      0

theorem nb057_fresh_190 :
    (nb057AlphaDummy210) ∉ (((Class.cv (nb057AlphaDummy203))).fv) := by
  simpa only [nb057AlphaDummy210] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy203))).fv) 0

theorem nb057_fresh_191 :
    (nb057AlphaDummy211) ∉ (((Class.cv (nb057AlphaDummy203))).fv) := by
  simpa only [nb057AlphaDummy211] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy203))).fv) 1

theorem nb057_distinct_192 : (nb057AlphaDummy210) ≠ (nb057AlphaDummy211) := by
  simpa only [nb057AlphaDummy210, nb057AlphaDummy211] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy203))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_193 (f : Var) :
    (nb057AlphaDummy212 f) ∉ (((Class.cv (nb057AlphaDummy205 f))).fv) := by
  simpa only [nb057AlphaDummy212] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy205 f))).fv) 0

theorem nb057_fresh_194 (f : Var) :
    (nb057AlphaDummy213 f) ∉ (((Class.cv (nb057AlphaDummy205 f))).fv) := by
  simpa only [nb057AlphaDummy213] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy205 f))).fv) 1

theorem nb057_distinct_195 (f : Var) :
    (nb057AlphaDummy212 f) ≠ (nb057AlphaDummy213 f) := by
  simpa only [nb057AlphaDummy212, nb057AlphaDummy213] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy205 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_196 :
    (nb057AlphaDummy216) ∉
      (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy216] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_197 :
    (nb057AlphaDummy217) ∉
      (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy217] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_198 :
    (nb057AlphaDummy218) ∉
      (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy218] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_199 : (nb057AlphaDummy216) ≠ (nb057AlphaDummy217) := by
  simpa only [nb057AlphaDummy216, nb057AlphaDummy217] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_200 : (nb057AlphaDummy216) ≠ (nb057AlphaDummy218) := by
  simpa only [nb057AlphaDummy216, nb057AlphaDummy218] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_201 : (nb057AlphaDummy217) ≠ (nb057AlphaDummy218) := by
  simpa only [nb057AlphaDummy217, nb057AlphaDummy218] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_202 (f : Var) :
    (nb057AlphaDummy219 f) ∉
      (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy219] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_203 (f : Var) :
    (nb057AlphaDummy220 f) ∉
      (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy220] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_204 (f : Var) :
    (nb057AlphaDummy221 f) ∉
      (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy221] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_205 (f : Var) :
    (nb057AlphaDummy219 f) ≠ (nb057AlphaDummy220 f) := by
  simpa only [nb057AlphaDummy219, nb057AlphaDummy220] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_206 (f : Var) :
    (nb057AlphaDummy219 f) ≠ (nb057AlphaDummy221 f) := by
  simpa only [nb057AlphaDummy219, nb057AlphaDummy221] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_207 (f : Var) :
    (nb057AlphaDummy220 f) ≠ (nb057AlphaDummy221 f) := by
  simpa only [nb057AlphaDummy220, nb057AlphaDummy221] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_208 :
    (nb057AlphaDummy228) ∉
      (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy217))).fv) :=
  by
  simpa only [nb057AlphaDummy228] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy217))).fv)
      0

theorem nb057_fresh_209 :
    (nb057AlphaDummy224) ∉
      (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv) :=
  by
  simpa only [nb057AlphaDummy224] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv)
      0

theorem nb057_fresh_210 :
    (nb057AlphaDummy230) ∉
      (((Class.cv (nb057AlphaDummy218))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv) :=
  by
  simpa only [nb057AlphaDummy230] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy218))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv)
      0

theorem nb057_fresh_211 (f : Var) :
    (nb057AlphaDummy229 f) ∉
      (((Class.cv (nb057AlphaDummy220 f))).fv ∪ ((Class.cv (nb057AlphaDummy220 f))).fv) :=
  by
  simpa only [nb057AlphaDummy229] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy220 f))).fv ∪ ((Class.cv (nb057AlphaDummy220 f))).fv)
      0

theorem nb057_fresh_212 (f : Var) :
    (nb057AlphaDummy225 f) ∉
      (((Class.cv (nb057AlphaDummy220 f))).fv ∪ ((Class.cv (nb057AlphaDummy221 f))).fv) :=
  by
  simpa only [nb057AlphaDummy225] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy220 f))).fv ∪ ((Class.cv (nb057AlphaDummy221 f))).fv)
      0

theorem nb057_fresh_213 (f : Var) :
    (nb057AlphaDummy231 f) ∉
      (((Class.cv (nb057AlphaDummy221 f))).fv ∪ ((Class.cv (nb057AlphaDummy221 f))).fv) :=
  by
  simpa only [nb057AlphaDummy231] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy221 f))).fv ∪ ((Class.cv (nb057AlphaDummy221 f))).fv)
      0

theorem nb057_fresh_214 :
    (nb057AlphaDummy242) ∉
      (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv) :=
  by
  simpa only [nb057AlphaDummy242] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv)
      0

theorem nb057_fresh_215 :
    (nb057AlphaDummy243) ∉
      (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv) :=
  by
  simpa only [nb057AlphaDummy243] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv)
      1

theorem nb057_distinct_216 : (nb057AlphaDummy242) ≠ (nb057AlphaDummy243) := by
  simpa only [nb057AlphaDummy242, nb057AlphaDummy243] using
    (freshVar_injective
      (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_217 (f : Var) :
    (nb057AlphaDummy244 f) ∉
      (((Class.cv (nb057AlphaDummy241 f))).fv ∪ ((Class.cv (nb057AlphaDummy240 f))).fv) :=
  by
  simpa only [nb057AlphaDummy244] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy241 f))).fv ∪ ((Class.cv (nb057AlphaDummy240 f))).fv)
      0

theorem nb057_fresh_218 (f : Var) :
    (nb057AlphaDummy245 f) ∉
      (((Class.cv (nb057AlphaDummy241 f))).fv ∪ ((Class.cv (nb057AlphaDummy240 f))).fv) :=
  by
  simpa only [nb057AlphaDummy245] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy241 f))).fv ∪ ((Class.cv (nb057AlphaDummy240 f))).fv)
      1

theorem nb057_distinct_219 (f : Var) :
    (nb057AlphaDummy244 f) ≠ (nb057AlphaDummy245 f) := by
  simpa only [nb057AlphaDummy244, nb057AlphaDummy245] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy241 f))).fv ∪
        ((Class.cv (nb057AlphaDummy240 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_220 :
    (nb057AlphaDummy250) ∉ (((Class.cv (nb057AlphaDummy243))).fv) := by
  simpa only [nb057AlphaDummy250] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy243))).fv) 0

theorem nb057_fresh_221 :
    (nb057AlphaDummy251) ∉ (((Class.cv (nb057AlphaDummy243))).fv) := by
  simpa only [nb057AlphaDummy251] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy243))).fv) 1

theorem nb057_distinct_222 : (nb057AlphaDummy250) ≠ (nb057AlphaDummy251) := by
  simpa only [nb057AlphaDummy250, nb057AlphaDummy251] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy243))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_223 (f : Var) :
    (nb057AlphaDummy252 f) ∉ (((Class.cv (nb057AlphaDummy245 f))).fv) := by
  simpa only [nb057AlphaDummy252] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy245 f))).fv) 0

theorem nb057_fresh_224 (f : Var) :
    (nb057AlphaDummy253 f) ∉ (((Class.cv (nb057AlphaDummy245 f))).fv) := by
  simpa only [nb057AlphaDummy253] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy245 f))).fv) 1

theorem nb057_distinct_225 (f : Var) :
    (nb057AlphaDummy252 f) ≠ (nb057AlphaDummy253 f) := by
  simpa only [nb057AlphaDummy252, nb057AlphaDummy253] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy245 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_226 :
    (nb057AlphaDummy256) ∉
      (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy256] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_227 :
    (nb057AlphaDummy257) ∉
      (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy257] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_228 :
    (nb057AlphaDummy258) ∉
      (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy258] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_229 : (nb057AlphaDummy256) ≠ (nb057AlphaDummy257) := by
  simpa only [nb057AlphaDummy256, nb057AlphaDummy257] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_230 : (nb057AlphaDummy256) ≠ (nb057AlphaDummy258) := by
  simpa only [nb057AlphaDummy256, nb057AlphaDummy258] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_231 : (nb057AlphaDummy257) ≠ (nb057AlphaDummy258) := by
  simpa only [nb057AlphaDummy257, nb057AlphaDummy258] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_232 (f : Var) :
    (nb057AlphaDummy259 f) ∉
      (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy259] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) 0

theorem nb057_fresh_233 (f : Var) :
    (nb057AlphaDummy260 f) ∉
      (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy260] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) 1

theorem nb057_fresh_234 (f : Var) :
    (nb057AlphaDummy261 f) ∉
      (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb057AlphaDummy261] using
    freshVar_not_mem (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) 2

theorem nb057_distinct_235 (f : Var) :
    (nb057AlphaDummy259 f) ≠ (nb057AlphaDummy260 f) := by
  simpa only [nb057AlphaDummy259, nb057AlphaDummy260] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_236 (f : Var) :
    (nb057AlphaDummy259 f) ≠ (nb057AlphaDummy261 f) := by
  simpa only [nb057AlphaDummy259, nb057AlphaDummy261] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_237 (f : Var) :
    (nb057AlphaDummy260 f) ≠ (nb057AlphaDummy261 f) := by
  simpa only [nb057AlphaDummy260, nb057AlphaDummy261] using
    (freshVar_injective (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_238 :
    (nb057AlphaDummy268) ∉
      (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy257))).fv) :=
  by
  simpa only [nb057AlphaDummy268] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy257))).fv)
      0

theorem nb057_fresh_239 :
    (nb057AlphaDummy264) ∉
      (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv) :=
  by
  simpa only [nb057AlphaDummy264] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv)
      0

theorem nb057_fresh_240 :
    (nb057AlphaDummy270) ∉
      (((Class.cv (nb057AlphaDummy258))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv) :=
  by
  simpa only [nb057AlphaDummy270] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy258))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv)
      0

theorem nb057_fresh_241 (f : Var) :
    (nb057AlphaDummy269 f) ∉
      (((Class.cv (nb057AlphaDummy260 f))).fv ∪ ((Class.cv (nb057AlphaDummy260 f))).fv) :=
  by
  simpa only [nb057AlphaDummy269] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy260 f))).fv ∪ ((Class.cv (nb057AlphaDummy260 f))).fv)
      0

theorem nb057_fresh_242 (f : Var) :
    (nb057AlphaDummy265 f) ∉
      (((Class.cv (nb057AlphaDummy260 f))).fv ∪ ((Class.cv (nb057AlphaDummy261 f))).fv) :=
  by
  simpa only [nb057AlphaDummy265] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy260 f))).fv ∪ ((Class.cv (nb057AlphaDummy261 f))).fv)
      0

theorem nb057_fresh_243 (f : Var) :
    (nb057AlphaDummy271 f) ∉
      (((Class.cv (nb057AlphaDummy261 f))).fv ∪ ((Class.cv (nb057AlphaDummy261 f))).fv) :=
  by
  simpa only [nb057AlphaDummy271] using
    freshVar_not_mem
      (((Class.cv (nb057AlphaDummy261 f))).fv ∪ ((Class.cv (nb057AlphaDummy261 f))).fv)
      0

theorem nb057_fresh_244 (f : Var) : (nb057AlphaDummy126 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb057AlphaDummy126] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb057_fresh_245 (f : Var) : (nb057AlphaDummy127 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb057AlphaDummy127] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb057_distinct_246 (f : Var) :
    (nb057AlphaDummy126 f) ≠ (nb057AlphaDummy127 f) := by
  simpa only [nb057AlphaDummy126, nb057AlphaDummy127] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_247 (f : Var) (a : Var) :
    (nb057AlphaDummy006 f a) ∉ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb057AlphaDummy006] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 0

theorem nb057_fresh_248 (f : Var) (a : Var) :
    (nb057AlphaDummy007 f a) ∉ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb057AlphaDummy007] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 1

theorem nb057_distinct_249 (f : Var) (a : Var) :
    (nb057AlphaDummy006 f a) ≠ (nb057AlphaDummy007 f a) := by
  simpa only [nb057AlphaDummy006, nb057AlphaDummy007] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_250 (f : Var) :
    (nb057AlphaDummy047 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb057AlphaDummy047] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0

theorem nb057_fresh_251 (f : Var) :
    (nb057AlphaDummy048 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb057AlphaDummy048] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1

theorem nb057_fresh_252 (f : Var) :
    (nb057AlphaDummy049 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb057AlphaDummy049] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2

theorem nb057_distinct_253 (f : Var) :
    (nb057AlphaDummy047 f) ≠ (nb057AlphaDummy048 f) := by
  simpa only [nb057AlphaDummy047, nb057AlphaDummy048] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb057_distinct_254 (f : Var) :
    (nb057AlphaDummy047 f) ≠ (nb057AlphaDummy049 f) := by
  simpa only [nb057AlphaDummy047, nb057AlphaDummy049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb057_distinct_255 (f : Var) :
    (nb057AlphaDummy048 f) ≠ (nb057AlphaDummy049 f) := by
  simpa only [nb057AlphaDummy048, nb057AlphaDummy049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb057_fresh_256 :
    (nb057AlphaDummy016) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy012)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy012)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy012))).fv) :=
  by
  simpa only [nb057AlphaDummy016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy012)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy012)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy012))).fv)
      0

theorem nb057_fresh_257 (f : Var) (a : Var) :
    (nb057AlphaDummy017 f a) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy014 f a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy014 f a)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy014 f a))).fv) :=
  by
  simpa only [nb057AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy014 f a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy014 f a)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy014 f a))).fv)
      0

theorem nb057_fresh_258 :
    (nb057AlphaDummy064) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy060)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy060)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy060))).fv) :=
  by
  simpa only [nb057AlphaDummy064] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy060)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy060)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy060))).fv)
      0

theorem nb057_fresh_259 (f : Var) :
    (nb057AlphaDummy065 f) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy062 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy062 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy062 f))).fv) :=
  by
  simpa only [nb057AlphaDummy065] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy062 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy062 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy062 f))).fv)
      0

theorem nb057_fresh_260 :
    (nb057AlphaDummy100) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy096)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy096)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy096))).fv) :=
  by
  simpa only [nb057AlphaDummy100] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy096)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy096)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy096))).fv)
      0

theorem nb057_fresh_261 (f : Var) :
    (nb057AlphaDummy101 f) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy098 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy098 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy098 f))).fv) :=
  by
  simpa only [nb057AlphaDummy101] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy098 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy098 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy098 f))).fv)
      0

theorem nb057_fresh_262 :
    (nb057AlphaDummy142) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy138)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy138)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy138))).fv) :=
  by
  simpa only [nb057AlphaDummy142] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy138)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy138)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy138))).fv)
      0

theorem nb057_fresh_263 (f : Var) :
    (nb057AlphaDummy143 f) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy140 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy140 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy140 f))).fv) :=
  by
  simpa only [nb057AlphaDummy143] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy140 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy140 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy140 f))).fv)
      0

theorem nb057_fresh_264 :
    (nb057AlphaDummy178) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy174)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy174)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy174))).fv) :=
  by
  simpa only [nb057AlphaDummy178] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy174)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy174)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy174))).fv)
      0

theorem nb057_fresh_265 (f : Var) :
    (nb057AlphaDummy179 f) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy176 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy176 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy176 f))).fv) :=
  by
  simpa only [nb057AlphaDummy179] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy176 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy176 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy176 f))).fv)
      0

theorem nb057_fresh_266 :
    (nb057AlphaDummy214) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy210)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy210)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy210))).fv) :=
  by
  simpa only [nb057AlphaDummy214] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy210)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy210)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy210))).fv)
      0

theorem nb057_fresh_267 (f : Var) :
    (nb057AlphaDummy215 f) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy212 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy212 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy212 f))).fv) :=
  by
  simpa only [nb057AlphaDummy215] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy212 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy212 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy212 f))).fv)
      0

theorem nb057_fresh_268 :
    (nb057AlphaDummy254) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy250)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy250)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy250))).fv) :=
  by
  simpa only [nb057AlphaDummy254] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy250)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy250)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy250))).fv)
      0

theorem nb057_fresh_269 (f : Var) :
    (nb057AlphaDummy255 f) ∉
      (((Wff.classMem (Class.cv (nb057AlphaDummy252 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy252 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy252 f))).fv) :=
  by
  simpa only [nb057AlphaDummy255] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057AlphaDummy252 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy252 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy252 f))).fv)
      0

theorem nb057_fresh_270 :
    (nb057AlphaDummy238) ∉
      (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb057AlphaDummy238] using
    freshVar_not_mem (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪ ((synCvv)).fv)
      0

theorem nb057_fresh_271 :
    (nb057AlphaDummy239) ∉
      (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb057AlphaDummy239] using
    freshVar_not_mem (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪ ((synCvv)).fv)
      1

theorem nb057_distinct_272 : (nb057AlphaDummy238) ≠ (nb057AlphaDummy239) := by
  simpa only [nb057AlphaDummy238, nb057AlphaDummy239] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪ ((synCvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb057_fresh_273 (f : Var) :
    (nb057AlphaDummy240 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb057AlphaDummy240] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0

theorem nb057_fresh_274 (f : Var) :
    (nb057AlphaDummy241 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb057AlphaDummy241] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1

theorem nb057_distinct_275 (f : Var) :
    (nb057AlphaDummy240 f) ≠ (nb057AlphaDummy241 f) := by
  simpa only [nb057AlphaDummy240, nb057AlphaDummy241] using
    (freshVar_injective (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_276 :
    (nb057AlphaDummy042) ∉
      (((synCcom (Class.cv (nb057AlphaDummy001))
            (synCcnv (Class.cv (nb057AlphaDummy001))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb057AlphaDummy042] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb057AlphaDummy001))
            (synCcnv (Class.cv (nb057AlphaDummy001))))).fv ∪ ((synCid)).fv)
      0

theorem nb057_fresh_277 (f : Var) :
    (nb057AlphaDummy043 f) ∉
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb057AlphaDummy043] using
    freshVar_not_mem
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0

theorem nb057_fresh_278 :
    (nb057AlphaDummy008) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy004)
              (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
                (Wff.classEq (Class.cv (nb057AlphaDummy004))
                  (synCphi (Class.cv (nb057AlphaDummy005)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy004)
              (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
                (Wff.classEq (Class.cv (nb057AlphaDummy004))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy008] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy004)
              (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
                (Wff.classEq (Class.cv (nb057AlphaDummy004))
                  (synCphi (Class.cv (nb057AlphaDummy005)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy004)
              (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
                (Wff.classEq (Class.cv (nb057AlphaDummy004))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_279 (f : Var) (a : Var) :
    (nb057AlphaDummy009 f a) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy006 f a)
              (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
                (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                  (synCphi (Class.cv (nb057AlphaDummy007 f a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy006 f a)
              (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
                (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy006 f a)
              (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
                (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                  (synCphi (Class.cv (nb057AlphaDummy007 f a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy006 f a)
              (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
                (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_280 :
    (nb057AlphaDummy056) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCphi (Class.cv (nb057AlphaDummy053)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy056] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCphi (Class.cv (nb057AlphaDummy053)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_281 (f : Var) :
    (nb057AlphaDummy057 f) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCphi (Class.cv (nb057AlphaDummy055 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy057] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCphi (Class.cv (nb057AlphaDummy055 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_282 :
    (nb057AlphaDummy092) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCphi (Class.cv (nb057AlphaDummy089)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy092] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCphi (Class.cv (nb057AlphaDummy089)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_283 (f : Var) :
    (nb057AlphaDummy093 f) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCphi (Class.cv (nb057AlphaDummy091 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy093] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCphi (Class.cv (nb057AlphaDummy091 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_284 :
    (nb057AlphaDummy134) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCphi (Class.cv (nb057AlphaDummy131)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy134] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCphi (Class.cv (nb057AlphaDummy131)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_285 (f : Var) :
    (nb057AlphaDummy135 f) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCphi (Class.cv (nb057AlphaDummy133 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy135] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCphi (Class.cv (nb057AlphaDummy133 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_286 :
    (nb057AlphaDummy170) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCphi (Class.cv (nb057AlphaDummy167)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy170] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCphi (Class.cv (nb057AlphaDummy167)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_287 (f : Var) :
    (nb057AlphaDummy171 f) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCphi (Class.cv (nb057AlphaDummy169 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy171] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCphi (Class.cv (nb057AlphaDummy169 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_288 :
    (nb057AlphaDummy206) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCphi (Class.cv (nb057AlphaDummy203)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy206] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCphi (Class.cv (nb057AlphaDummy203)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_289 (f : Var) :
    (nb057AlphaDummy207 f) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCphi (Class.cv (nb057AlphaDummy205 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy207] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCphi (Class.cv (nb057AlphaDummy205 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_290 :
    (nb057AlphaDummy246) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCphi (Class.cv (nb057AlphaDummy243)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy246] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCphi (Class.cv (nb057AlphaDummy243)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_291 (f : Var) :
    (nb057AlphaDummy247 f) ∉
      (((synCcompl (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCphi (Class.cv (nb057AlphaDummy245 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb057AlphaDummy247] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCphi (Class.cv (nb057AlphaDummy245 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb057_fresh_292 :
    (nb057AlphaDummy028) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy019)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy020)))).fv) :=
  by
  simpa only [nb057AlphaDummy028] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy019)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy020)))).fv)
      0

theorem nb057_fresh_293 (f : Var) (a : Var) :
    (nb057AlphaDummy029 f a) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy022 f a)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy023 f a)))).fv) :=
  by
  simpa only [nb057AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy022 f a)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy023 f a)))).fv)
      0

theorem nb057_fresh_294 :
    (nb057AlphaDummy076) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy067)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy068)))).fv) :=
  by
  simpa only [nb057AlphaDummy076] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy067)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy068)))).fv)
      0

theorem nb057_fresh_295 (f : Var) :
    (nb057AlphaDummy077 f) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy070 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy071 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy077] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy070 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy071 f)))).fv)
      0

theorem nb057_fresh_296 :
    (nb057AlphaDummy112) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy103)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy104)))).fv) :=
  by
  simpa only [nb057AlphaDummy112] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy103)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy104)))).fv)
      0

theorem nb057_fresh_297 (f : Var) :
    (nb057AlphaDummy113 f) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy106 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy107 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy113] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy106 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy107 f)))).fv)
      0

theorem nb057_fresh_298 :
    (nb057AlphaDummy154) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy145)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy146)))).fv) :=
  by
  simpa only [nb057AlphaDummy154] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy145)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy146)))).fv)
      0

theorem nb057_fresh_299 (f : Var) :
    (nb057AlphaDummy155 f) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy148 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy149 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy155] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy148 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy149 f)))).fv)
      0

theorem nb057_fresh_300 :
    (nb057AlphaDummy190) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy181)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy182)))).fv) :=
  by
  simpa only [nb057AlphaDummy190] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy181)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy182)))).fv)
      0

theorem nb057_fresh_301 (f : Var) :
    (nb057AlphaDummy191 f) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy184 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy185 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy191] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy184 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy185 f)))).fv)
      0

theorem nb057_fresh_302 :
    (nb057AlphaDummy226) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy217)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy218)))).fv) :=
  by
  simpa only [nb057AlphaDummy226] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy217)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy218)))).fv)
      0

theorem nb057_fresh_303 (f : Var) :
    (nb057AlphaDummy227 f) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy220 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy221 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy227] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy220 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy221 f)))).fv)
      0

theorem nb057_fresh_304 :
    (nb057AlphaDummy266) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy257)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy258)))).fv) :=
  by
  simpa only [nb057AlphaDummy266] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy257)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy258)))).fv)
      0

theorem nb057_fresh_305 (f : Var) :
    (nb057AlphaDummy267 f) ∉
      (((synCcompl (Class.cv (nb057AlphaDummy260 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy261 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy267] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb057AlphaDummy260 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy261 f)))).fv)
      0

theorem nb057_fresh_306 :
    (nb057AlphaDummy036) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy005))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy036] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy005))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_307 (f : Var) (a : Var) :
    (nb057AlphaDummy037 f a) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy007 f a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy007 f a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_308 :
    (nb057AlphaDummy084) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy053))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy084] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy053))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_309 (f : Var) :
    (nb057AlphaDummy085 f) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy055 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy085] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy055 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_310 :
    (nb057AlphaDummy120) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy089))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy120] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy089))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_311 (f : Var) :
    (nb057AlphaDummy121 f) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy091 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy121] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy091 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_312 :
    (nb057AlphaDummy162) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy131))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy162] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy131))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_313 (f : Var) :
    (nb057AlphaDummy163 f) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy133 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy163] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy133 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_314 :
    (nb057AlphaDummy198) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy167))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy198] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy167))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_315 (f : Var) :
    (nb057AlphaDummy199 f) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy169 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy199] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy169 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_316 :
    (nb057AlphaDummy234) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy203))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy234] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy203))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_317 (f : Var) :
    (nb057AlphaDummy235 f) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy205 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy235] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy205 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_318 :
    (nb057AlphaDummy274) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy243))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy274] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy243))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_319 (f : Var) :
    (nb057AlphaDummy275 f) ∉
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy245 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb057AlphaDummy275] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy245 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb057_fresh_320 :
    (nb057AlphaDummy024) ∉
      (((synCnin (Class.cv (nb057AlphaDummy019)) (Class.cv (nb057AlphaDummy020)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy019))
            (Class.cv (nb057AlphaDummy020)))).fv) :=
  by
  simpa only [nb057AlphaDummy024] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy019)) (Class.cv (nb057AlphaDummy020)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy019)) (Class.cv (nb057AlphaDummy020)))).fv)
      0

theorem nb057_fresh_321 (f : Var) (a : Var) :
    (nb057AlphaDummy025 f a) ∉
      (((synCnin (Class.cv (nb057AlphaDummy022 f a))
            (Class.cv (nb057AlphaDummy023 f a)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy022 f a))
            (Class.cv (nb057AlphaDummy023 f a)))).fv) :=
  by
  simpa only [nb057AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy022 f a))
            (Class.cv (nb057AlphaDummy023 f a)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy022 f a))
            (Class.cv (nb057AlphaDummy023 f a)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
