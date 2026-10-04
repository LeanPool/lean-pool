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

/-! Certificates from `NAR4C068C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_000`. -/
@[expose]
noncomputable def nb068AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_001`. -/
@[expose]
noncomputable def nb068AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_002`. -/
@[expose]
noncomputable def nb068AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_003`. -/
@[expose]
noncomputable def nb068AlphaDummy003 : Var :=
  (freshVar
    (({(nb068AlphaDummy001)} : Finset Var) ∪ ({(nb068AlphaDummy002)} : Finset Var) ∪
      ((synWex (nb068AlphaDummy000)
          (synWf1o (Class.cv (nb068AlphaDummy000)) (Class.cv (nb068AlphaDummy001))
            (Class.cv (nb068AlphaDummy002))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_004`. -/
@[expose]
noncomputable def nb068AlphaDummy004 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((synWex f (synWf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_005`. -/
@[expose]
noncomputable def nb068AlphaDummy005 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_006`. -/
@[expose]
noncomputable def nb068AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_007`. -/
@[expose]
noncomputable def nb068AlphaDummy007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_008`. -/
@[expose]
noncomputable def nb068AlphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_009`. -/
@[expose]
noncomputable def nb068AlphaDummy009 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCphi (Class.cv (nb068AlphaDummy006)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_010`. -/
@[expose]
noncomputable def nb068AlphaDummy010 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCphi (Class.cv (nb068AlphaDummy008 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_011`. -/
@[expose]
noncomputable def nb068AlphaDummy011 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy005)
          (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
            (Wff.classEq (Class.cv (nb068AlphaDummy005))
              (synCphi (Class.cv (nb068AlphaDummy006))))))).fv ∪
      ((Class.cab (nb068AlphaDummy005)
          (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
            (Wff.classEq (Class.cv (nb068AlphaDummy005))
              (synCphi (Class.cv (nb068AlphaDummy006))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_012`. -/
@[expose]
noncomputable def nb068AlphaDummy012 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy007 x y)
          (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
              (synCphi (Class.cv (nb068AlphaDummy008 x y))))))).fv ∪
      ((Class.cab (nb068AlphaDummy007 x y) (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
              (synCphi (Class.cv (nb068AlphaDummy008 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_013`. -/
@[expose]
noncomputable def nb068AlphaDummy013 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_014`. -/
@[expose]
noncomputable def nb068AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy006))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_015`. -/
@[expose]
noncomputable def nb068AlphaDummy015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy008 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_016`. -/
@[expose]
noncomputable def nb068AlphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy008 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_017`. -/
@[expose]
noncomputable def nb068AlphaDummy017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy013)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy013)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy013))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_018`. -/
@[expose]
noncomputable def nb068AlphaDummy018 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy015 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy015 x y)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy015 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_019`. -/
@[expose]
noncomputable def nb068AlphaDummy019 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_020`. -/
@[expose]
noncomputable def nb068AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_021`. -/
@[expose]
noncomputable def nb068AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_022`. -/
@[expose]
noncomputable def nb068AlphaDummy022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_023`. -/
@[expose]
noncomputable def nb068AlphaDummy023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_024`. -/
@[expose]
noncomputable def nb068AlphaDummy024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_025`. -/
@[expose]
noncomputable def nb068AlphaDummy025 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy020))
          (Class.cv (nb068AlphaDummy021)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_026`. -/
@[expose]
noncomputable def nb068AlphaDummy026 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy023 x y))
          (Class.cv (nb068AlphaDummy024 x y)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy023 x y))
          (Class.cv (nb068AlphaDummy024 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_027`. -/
@[expose]
noncomputable def nb068AlphaDummy027 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_028`. -/
@[expose]
noncomputable def nb068AlphaDummy028 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
      ((Class.cv (nb068AlphaDummy024 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_029`. -/
@[expose]
noncomputable def nb068AlphaDummy029 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy020)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_030`. -/
@[expose]
noncomputable def nb068AlphaDummy030 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy023 x y)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy024 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_031`. -/
@[expose]
noncomputable def nb068AlphaDummy031 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_032`. -/
@[expose]
noncomputable def nb068AlphaDummy032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
      ((Class.cv (nb068AlphaDummy023 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_033`. -/
@[expose]
noncomputable def nb068AlphaDummy033 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy021))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_034`. -/
@[expose]
noncomputable def nb068AlphaDummy034 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy024 x y))).fv ∪
      ((Class.cv (nb068AlphaDummy024 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_035`. -/
@[expose]
noncomputable def nb068AlphaDummy035 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy005)
          (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
            (Wff.classEq (Class.cv (nb068AlphaDummy005))
              (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy005)
          (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
            (Wff.classEq (Class.cv (nb068AlphaDummy005))
              (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_036`. -/
@[expose]
noncomputable def nb068AlphaDummy036 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy007 x y)
          (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
              (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy007 x y)
          (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
              (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_037`. -/
@[expose]
noncomputable def nb068AlphaDummy037 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy006))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_038`. -/
@[expose]
noncomputable def nb068AlphaDummy038 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy008 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_039`. -/
@[expose]
noncomputable def nb068AlphaDummy039 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy006)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy006)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_040`. -/
@[expose]
noncomputable def nb068AlphaDummy040 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy008 x y)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy008 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_041`. -/
@[expose]
noncomputable def nb068AlphaDummy041 : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb068AlphaDummy000))
            (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
          (synCcom (Class.cv (nb068AlphaDummy000))
            (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_042`. -/
@[expose]
noncomputable def nb068AlphaDummy042 (f : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_043`. -/
@[expose]
noncomputable def nb068AlphaDummy043 : Var :=
  (freshVar (((synCcom (Class.cv (nb068AlphaDummy000))
          (synCcnv (Class.cv (nb068AlphaDummy000))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_044`. -/
@[expose]
noncomputable def nb068AlphaDummy044 (f : Var) : Var :=
  (freshVar (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_045`. -/
@[expose]
noncomputable def nb068AlphaDummy045 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_046`. -/
@[expose]
noncomputable def nb068AlphaDummy046 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_047`. -/
@[expose]
noncomputable def nb068AlphaDummy047 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_048`. -/
@[expose]
noncomputable def nb068AlphaDummy048 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_049`. -/
@[expose]
noncomputable def nb068AlphaDummy049 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_050`. -/
@[expose]
noncomputable def nb068AlphaDummy050 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_051`. -/
@[expose]
noncomputable def nb068AlphaDummy051 : Var :=
  (freshVar
    (({(nb068AlphaDummy045)} : Finset Var) ∪ ({(nb068AlphaDummy046)} : Finset Var) ∪
      ((synWex (nb068AlphaDummy047) (synWa (synWbr (Class.cv (nb068AlphaDummy045))
              (synCcnv (Class.cv (nb068AlphaDummy000))) (Class.cv (nb068AlphaDummy047)))
            (synWbr (Class.cv (nb068AlphaDummy047)) (Class.cv (nb068AlphaDummy000))
              (Class.cv (nb068AlphaDummy046)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_052`. -/
@[expose]
noncomputable def nb068AlphaDummy052 (f : Var) : Var :=
  (freshVar (({(nb068AlphaDummy048 f)} : Finset Var) ∪
        ({(nb068AlphaDummy049 f)} : Finset Var) ∪ ((synWex (nb068AlphaDummy050 f) (synWa
            (synWbr (Class.cv (nb068AlphaDummy048 f)) (synCcnv (Class.cv f))
              (Class.cv (nb068AlphaDummy050 f)))
            (synWbr (Class.cv (nb068AlphaDummy050 f)) (Class.cv f)
              (Class.cv (nb068AlphaDummy049 f)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_053`. -/
@[expose]
noncomputable def nb068AlphaDummy053 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_054`. -/
@[expose]
noncomputable def nb068AlphaDummy054 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_055`. -/
@[expose]
noncomputable def nb068AlphaDummy055 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy048 f))).fv ∪
      ((Class.cv (nb068AlphaDummy049 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_056`. -/
@[expose]
noncomputable def nb068AlphaDummy056 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy048 f))).fv ∪
      ((Class.cv (nb068AlphaDummy049 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_057`. -/
@[expose]
noncomputable def nb068AlphaDummy057 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCphi (Class.cv (nb068AlphaDummy054)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_058`. -/
@[expose]
noncomputable def nb068AlphaDummy058 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCphi (Class.cv (nb068AlphaDummy056 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_059`. -/
@[expose]
noncomputable def nb068AlphaDummy059 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy053)
          (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
            (Wff.classEq (Class.cv (nb068AlphaDummy053))
              (synCphi (Class.cv (nb068AlphaDummy054))))))).fv ∪
      ((Class.cab (nb068AlphaDummy053)
          (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
            (Wff.classEq (Class.cv (nb068AlphaDummy053))
              (synCphi (Class.cv (nb068AlphaDummy054))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_060`. -/
@[expose]
noncomputable def nb068AlphaDummy060 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy055 f)
          (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
              (synCphi (Class.cv (nb068AlphaDummy056 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy055 f)
          (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
              (synCphi (Class.cv (nb068AlphaDummy056 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_061`. -/
@[expose]
noncomputable def nb068AlphaDummy061 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy054))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_062`. -/
@[expose]
noncomputable def nb068AlphaDummy062 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy054))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_063`. -/
@[expose]
noncomputable def nb068AlphaDummy063 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy056 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_064`. -/
@[expose]
noncomputable def nb068AlphaDummy064 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy056 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_065`. -/
@[expose]
noncomputable def nb068AlphaDummy065 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy061)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy061)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy061))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_066`. -/
@[expose]
noncomputable def nb068AlphaDummy066 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy063 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy063 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy063 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_067`. -/
@[expose]
noncomputable def nb068AlphaDummy067 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_068`. -/
@[expose]
noncomputable def nb068AlphaDummy068 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_069`. -/
@[expose]
noncomputable def nb068AlphaDummy069 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_070`. -/
@[expose]
noncomputable def nb068AlphaDummy070 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_071`. -/
@[expose]
noncomputable def nb068AlphaDummy071 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_072`. -/
@[expose]
noncomputable def nb068AlphaDummy072 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_073`. -/
@[expose]
noncomputable def nb068AlphaDummy073 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy068))
          (Class.cv (nb068AlphaDummy069)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_074`. -/
@[expose]
noncomputable def nb068AlphaDummy074 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy071 f))
          (Class.cv (nb068AlphaDummy072 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy071 f)) (Class.cv (nb068AlphaDummy072 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_075`. -/
@[expose]
noncomputable def nb068AlphaDummy075 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_076`. -/
@[expose]
noncomputable def nb068AlphaDummy076 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy071 f))).fv ∪
      ((Class.cv (nb068AlphaDummy072 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_077`. -/
@[expose]
noncomputable def nb068AlphaDummy077 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy068)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy069)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_078`. -/
@[expose]
noncomputable def nb068AlphaDummy078 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy071 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy072 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_079`. -/
@[expose]
noncomputable def nb068AlphaDummy079 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy068))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_080`. -/
@[expose]
noncomputable def nb068AlphaDummy080 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy071 f))).fv ∪
      ((Class.cv (nb068AlphaDummy071 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_081`. -/
@[expose]
noncomputable def nb068AlphaDummy081 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy069))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_082`. -/
@[expose]
noncomputable def nb068AlphaDummy082 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy072 f))).fv ∪
      ((Class.cv (nb068AlphaDummy072 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_083`. -/
@[expose]
noncomputable def nb068AlphaDummy083 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy053)
          (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
            (Wff.classEq (Class.cv (nb068AlphaDummy053))
              (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy053)
          (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
            (Wff.classEq (Class.cv (nb068AlphaDummy053))
              (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_084`. -/
@[expose]
noncomputable def nb068AlphaDummy084 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy055 f)
          (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy055 f)
          (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_085`. -/
@[expose]
noncomputable def nb068AlphaDummy085 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy054))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_086`. -/
@[expose]
noncomputable def nb068AlphaDummy086 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy056 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_087`. -/
@[expose]
noncomputable def nb068AlphaDummy087 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy054)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy054)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_088`. -/
@[expose]
noncomputable def nb068AlphaDummy088 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy056 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy056 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_089`. -/
@[expose]
noncomputable def nb068AlphaDummy089 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_090`. -/
@[expose]
noncomputable def nb068AlphaDummy090 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_091`. -/
@[expose]
noncomputable def nb068AlphaDummy091 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy048 f))).fv ∪
      ((Class.cv (nb068AlphaDummy050 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_092`. -/
@[expose]
noncomputable def nb068AlphaDummy092 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy048 f))).fv ∪
      ((Class.cv (nb068AlphaDummy050 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_093`. -/
@[expose]
noncomputable def nb068AlphaDummy093 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCphi (Class.cv (nb068AlphaDummy090)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_094`. -/
@[expose]
noncomputable def nb068AlphaDummy094 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCphi (Class.cv (nb068AlphaDummy092 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_095`. -/
@[expose]
noncomputable def nb068AlphaDummy095 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy089)
          (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
            (Wff.classEq (Class.cv (nb068AlphaDummy089))
              (synCphi (Class.cv (nb068AlphaDummy090))))))).fv ∪
      ((Class.cab (nb068AlphaDummy089)
          (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
            (Wff.classEq (Class.cv (nb068AlphaDummy089))
              (synCphi (Class.cv (nb068AlphaDummy090))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_096`. -/
@[expose]
noncomputable def nb068AlphaDummy096 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy091 f)
          (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
              (synCphi (Class.cv (nb068AlphaDummy092 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy091 f)
          (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
              (synCphi (Class.cv (nb068AlphaDummy092 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_097`. -/
@[expose]
noncomputable def nb068AlphaDummy097 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy090))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_098`. -/
@[expose]
noncomputable def nb068AlphaDummy098 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy090))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_099`. -/
@[expose]
noncomputable def nb068AlphaDummy099 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy092 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_100`. -/
@[expose]
noncomputable def nb068AlphaDummy100 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy092 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_101`. -/
@[expose]
noncomputable def nb068AlphaDummy101 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy097)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy097)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy097))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_102`. -/
@[expose]
noncomputable def nb068AlphaDummy102 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy099 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy099 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy099 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_103`. -/
@[expose]
noncomputable def nb068AlphaDummy103 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_104`. -/
@[expose]
noncomputable def nb068AlphaDummy104 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_105`. -/
@[expose]
noncomputable def nb068AlphaDummy105 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_106`. -/
@[expose]
noncomputable def nb068AlphaDummy106 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_107`. -/
@[expose]
noncomputable def nb068AlphaDummy107 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_108`. -/
@[expose]
noncomputable def nb068AlphaDummy108 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_109`. -/
@[expose]
noncomputable def nb068AlphaDummy109 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy104))
          (Class.cv (nb068AlphaDummy105)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_110`. -/
@[expose]
noncomputable def nb068AlphaDummy110 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy107 f))
          (Class.cv (nb068AlphaDummy108 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy107 f)) (Class.cv (nb068AlphaDummy108 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_111`. -/
@[expose]
noncomputable def nb068AlphaDummy111 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_112`. -/
@[expose]
noncomputable def nb068AlphaDummy112 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy107 f))).fv ∪
      ((Class.cv (nb068AlphaDummy108 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_113`. -/
@[expose]
noncomputable def nb068AlphaDummy113 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy104)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy105)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_114`. -/
@[expose]
noncomputable def nb068AlphaDummy114 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy107 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy108 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_115`. -/
@[expose]
noncomputable def nb068AlphaDummy115 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy104))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_116`. -/
@[expose]
noncomputable def nb068AlphaDummy116 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy107 f))).fv ∪
      ((Class.cv (nb068AlphaDummy107 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_117`. -/
@[expose]
noncomputable def nb068AlphaDummy117 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy105))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_118`. -/
@[expose]
noncomputable def nb068AlphaDummy118 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy108 f))).fv ∪
      ((Class.cv (nb068AlphaDummy108 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_119`. -/
@[expose]
noncomputable def nb068AlphaDummy119 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy089)
          (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
            (Wff.classEq (Class.cv (nb068AlphaDummy089))
              (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy089)
          (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
            (Wff.classEq (Class.cv (nb068AlphaDummy089))
              (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_120`. -/
@[expose]
noncomputable def nb068AlphaDummy120 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy091 f)
          (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy091 f)
          (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_121`. -/
@[expose]
noncomputable def nb068AlphaDummy121 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy090))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_122`. -/
@[expose]
noncomputable def nb068AlphaDummy122 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy092 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_123`. -/
@[expose]
noncomputable def nb068AlphaDummy123 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy090)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy090)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_124`. -/
@[expose]
noncomputable def nb068AlphaDummy124 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy092 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy092 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_125`. -/
@[expose]
noncomputable def nb068AlphaDummy125 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_126`. -/
@[expose]
noncomputable def nb068AlphaDummy126 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_127`. -/
@[expose]
noncomputable def nb068AlphaDummy127 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_128`. -/
@[expose]
noncomputable def nb068AlphaDummy128 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_129`. -/
@[expose]
noncomputable def nb068AlphaDummy129 : Var :=
  (freshVar
    (({(nb068AlphaDummy125)} : Finset Var) ∪ ({(nb068AlphaDummy126)} : Finset Var) ∪
      ((synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
          (Class.cv (nb068AlphaDummy125)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_130`. -/
@[expose]
noncomputable def nb068AlphaDummy130 (f : Var) : Var :=
  (freshVar (({(nb068AlphaDummy127 f)} : Finset Var) ∪
        ({(nb068AlphaDummy128 f)} : Finset Var) ∪
      ((synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
          (Class.cv (nb068AlphaDummy127 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_131`. -/
@[expose]
noncomputable def nb068AlphaDummy131 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_132`. -/
@[expose]
noncomputable def nb068AlphaDummy132 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_133`. -/
@[expose]
noncomputable def nb068AlphaDummy133 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy127 f))).fv ∪
      ((Class.cv (nb068AlphaDummy128 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_134`. -/
@[expose]
noncomputable def nb068AlphaDummy134 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy127 f))).fv ∪
      ((Class.cv (nb068AlphaDummy128 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_135`. -/
@[expose]
noncomputable def nb068AlphaDummy135 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCphi (Class.cv (nb068AlphaDummy132)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_136`. -/
@[expose]
noncomputable def nb068AlphaDummy136 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCphi (Class.cv (nb068AlphaDummy134 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_137`. -/
@[expose]
noncomputable def nb068AlphaDummy137 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy131)
          (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
            (Wff.classEq (Class.cv (nb068AlphaDummy131))
              (synCphi (Class.cv (nb068AlphaDummy132))))))).fv ∪
      ((Class.cab (nb068AlphaDummy131)
          (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
            (Wff.classEq (Class.cv (nb068AlphaDummy131))
              (synCphi (Class.cv (nb068AlphaDummy132))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_138`. -/
@[expose]
noncomputable def nb068AlphaDummy138 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy133 f)
          (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
              (synCphi (Class.cv (nb068AlphaDummy134 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy133 f)
          (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
              (synCphi (Class.cv (nb068AlphaDummy134 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_139`. -/
@[expose]
noncomputable def nb068AlphaDummy139 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy132))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_140`. -/
@[expose]
noncomputable def nb068AlphaDummy140 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy132))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_141`. -/
@[expose]
noncomputable def nb068AlphaDummy141 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy134 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_142`. -/
@[expose]
noncomputable def nb068AlphaDummy142 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy134 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_143`. -/
@[expose]
noncomputable def nb068AlphaDummy143 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy139))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_144`. -/
@[expose]
noncomputable def nb068AlphaDummy144 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy141 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_145`. -/
@[expose]
noncomputable def nb068AlphaDummy145 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_146`. -/
@[expose]
noncomputable def nb068AlphaDummy146 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_147`. -/
@[expose]
noncomputable def nb068AlphaDummy147 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_148`. -/
@[expose]
noncomputable def nb068AlphaDummy148 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_149`. -/
@[expose]
noncomputable def nb068AlphaDummy149 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_150`. -/
@[expose]
noncomputable def nb068AlphaDummy150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_151`. -/
@[expose]
noncomputable def nb068AlphaDummy151 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy146))
          (Class.cv (nb068AlphaDummy147)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_152`. -/
@[expose]
noncomputable def nb068AlphaDummy152 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy149 f))
          (Class.cv (nb068AlphaDummy150 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy149 f)) (Class.cv (nb068AlphaDummy150 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_153`. -/
@[expose]
noncomputable def nb068AlphaDummy153 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_154`. -/
@[expose]
noncomputable def nb068AlphaDummy154 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy149 f))).fv ∪
      ((Class.cv (nb068AlphaDummy150 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_155`. -/
@[expose]
noncomputable def nb068AlphaDummy155 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy146)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy147)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_156`. -/
@[expose]
noncomputable def nb068AlphaDummy156 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy149 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy150 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_157`. -/
@[expose]
noncomputable def nb068AlphaDummy157 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy146))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_158`. -/
@[expose]
noncomputable def nb068AlphaDummy158 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy149 f))).fv ∪
      ((Class.cv (nb068AlphaDummy149 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_159`. -/
@[expose]
noncomputable def nb068AlphaDummy159 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy147))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_160`. -/
@[expose]
noncomputable def nb068AlphaDummy160 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy150 f))).fv ∪
      ((Class.cv (nb068AlphaDummy150 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_161`. -/
@[expose]
noncomputable def nb068AlphaDummy161 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy131)
          (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
            (Wff.classEq (Class.cv (nb068AlphaDummy131))
              (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy131)
          (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
            (Wff.classEq (Class.cv (nb068AlphaDummy131))
              (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_162`. -/
@[expose]
noncomputable def nb068AlphaDummy162 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy133 f)
          (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy133 f)
          (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_163`. -/
@[expose]
noncomputable def nb068AlphaDummy163 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy132))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_164`. -/
@[expose]
noncomputable def nb068AlphaDummy164 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy134 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_165`. -/
@[expose]
noncomputable def nb068AlphaDummy165 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy132)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy132)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_166`. -/
@[expose]
noncomputable def nb068AlphaDummy166 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy134 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy134 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_167`. -/
@[expose]
noncomputable def nb068AlphaDummy167 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_168`. -/
@[expose]
noncomputable def nb068AlphaDummy168 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_169`. -/
@[expose]
noncomputable def nb068AlphaDummy169 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy128 f))).fv ∪
      ((Class.cv (nb068AlphaDummy127 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_170`. -/
@[expose]
noncomputable def nb068AlphaDummy170 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy128 f))).fv ∪
      ((Class.cv (nb068AlphaDummy127 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_171`. -/
@[expose]
noncomputable def nb068AlphaDummy171 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCphi (Class.cv (nb068AlphaDummy168)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_172`. -/
@[expose]
noncomputable def nb068AlphaDummy172 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCphi (Class.cv (nb068AlphaDummy170 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_173`. -/
@[expose]
noncomputable def nb068AlphaDummy173 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy167)
          (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
            (Wff.classEq (Class.cv (nb068AlphaDummy167))
              (synCphi (Class.cv (nb068AlphaDummy168))))))).fv ∪
      ((Class.cab (nb068AlphaDummy167)
          (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
            (Wff.classEq (Class.cv (nb068AlphaDummy167))
              (synCphi (Class.cv (nb068AlphaDummy168))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_174`. -/
@[expose]
noncomputable def nb068AlphaDummy174 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy169 f)
          (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
              (synCphi (Class.cv (nb068AlphaDummy170 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy169 f)
          (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
              (synCphi (Class.cv (nb068AlphaDummy170 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_175`. -/
@[expose]
noncomputable def nb068AlphaDummy175 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy168))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_176`. -/
@[expose]
noncomputable def nb068AlphaDummy176 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy168))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_177`. -/
@[expose]
noncomputable def nb068AlphaDummy177 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy170 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_178`. -/
@[expose]
noncomputable def nb068AlphaDummy178 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy170 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_179`. -/
@[expose]
noncomputable def nb068AlphaDummy179 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy175))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_180`. -/
@[expose]
noncomputable def nb068AlphaDummy180 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy177 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_181`. -/
@[expose]
noncomputable def nb068AlphaDummy181 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_182`. -/
@[expose]
noncomputable def nb068AlphaDummy182 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_183`. -/
@[expose]
noncomputable def nb068AlphaDummy183 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_184`. -/
@[expose]
noncomputable def nb068AlphaDummy184 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_185`. -/
@[expose]
noncomputable def nb068AlphaDummy185 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_186`. -/
@[expose]
noncomputable def nb068AlphaDummy186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_187`. -/
@[expose]
noncomputable def nb068AlphaDummy187 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy182))
          (Class.cv (nb068AlphaDummy183)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_188`. -/
@[expose]
noncomputable def nb068AlphaDummy188 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy185 f))
          (Class.cv (nb068AlphaDummy186 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy185 f)) (Class.cv (nb068AlphaDummy186 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_189`. -/
@[expose]
noncomputable def nb068AlphaDummy189 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_190`. -/
@[expose]
noncomputable def nb068AlphaDummy190 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy185 f))).fv ∪
      ((Class.cv (nb068AlphaDummy186 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_191`. -/
@[expose]
noncomputable def nb068AlphaDummy191 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy182)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy183)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_192`. -/
@[expose]
noncomputable def nb068AlphaDummy192 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy185 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy186 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_193`. -/
@[expose]
noncomputable def nb068AlphaDummy193 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy182))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_194`. -/
@[expose]
noncomputable def nb068AlphaDummy194 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy185 f))).fv ∪
      ((Class.cv (nb068AlphaDummy185 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_195`. -/
@[expose]
noncomputable def nb068AlphaDummy195 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy183))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_196`. -/
@[expose]
noncomputable def nb068AlphaDummy196 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy186 f))).fv ∪
      ((Class.cv (nb068AlphaDummy186 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_197`. -/
@[expose]
noncomputable def nb068AlphaDummy197 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy167)
          (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
            (Wff.classEq (Class.cv (nb068AlphaDummy167))
              (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy167)
          (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
            (Wff.classEq (Class.cv (nb068AlphaDummy167))
              (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_198`. -/
@[expose]
noncomputable def nb068AlphaDummy198 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy169 f)
          (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy169 f)
          (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_199`. -/
@[expose]
noncomputable def nb068AlphaDummy199 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy168))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_200`. -/
@[expose]
noncomputable def nb068AlphaDummy200 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy170 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_201`. -/
@[expose]
noncomputable def nb068AlphaDummy201 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy168)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy168)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_202`. -/
@[expose]
noncomputable def nb068AlphaDummy202 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy170 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy170 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_203`. -/
@[expose]
noncomputable def nb068AlphaDummy203 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_204`. -/
@[expose]
noncomputable def nb068AlphaDummy204 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_205`. -/
@[expose]
noncomputable def nb068AlphaDummy205 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy050 f))).fv ∪
      ((Class.cv (nb068AlphaDummy049 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_206`. -/
@[expose]
noncomputable def nb068AlphaDummy206 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy050 f))).fv ∪
      ((Class.cv (nb068AlphaDummy049 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_207`. -/
@[expose]
noncomputable def nb068AlphaDummy207 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCphi (Class.cv (nb068AlphaDummy204)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_208`. -/
@[expose]
noncomputable def nb068AlphaDummy208 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCphi (Class.cv (nb068AlphaDummy206 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_209`. -/
@[expose]
noncomputable def nb068AlphaDummy209 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy203)
          (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
            (Wff.classEq (Class.cv (nb068AlphaDummy203))
              (synCphi (Class.cv (nb068AlphaDummy204))))))).fv ∪
      ((Class.cab (nb068AlphaDummy203)
          (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
            (Wff.classEq (Class.cv (nb068AlphaDummy203))
              (synCphi (Class.cv (nb068AlphaDummy204))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_210`. -/
@[expose]
noncomputable def nb068AlphaDummy210 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy205 f)
          (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
              (synCphi (Class.cv (nb068AlphaDummy206 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy205 f)
          (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
              (synCphi (Class.cv (nb068AlphaDummy206 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_211`. -/
@[expose]
noncomputable def nb068AlphaDummy211 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy204))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_212`. -/
@[expose]
noncomputable def nb068AlphaDummy212 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy204))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_213`. -/
@[expose]
noncomputable def nb068AlphaDummy213 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy206 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_214`. -/
@[expose]
noncomputable def nb068AlphaDummy214 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy206 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_215`. -/
@[expose]
noncomputable def nb068AlphaDummy215 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy211)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy211)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy211))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_216`. -/
@[expose]
noncomputable def nb068AlphaDummy216 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy213 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy213 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy213 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_217`. -/
@[expose]
noncomputable def nb068AlphaDummy217 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_218`. -/
@[expose]
noncomputable def nb068AlphaDummy218 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_219`. -/
@[expose]
noncomputable def nb068AlphaDummy219 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_220`. -/
@[expose]
noncomputable def nb068AlphaDummy220 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_221`. -/
@[expose]
noncomputable def nb068AlphaDummy221 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_222`. -/
@[expose]
noncomputable def nb068AlphaDummy222 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_223`. -/
@[expose]
noncomputable def nb068AlphaDummy223 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy218))
          (Class.cv (nb068AlphaDummy219)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_224`. -/
@[expose]
noncomputable def nb068AlphaDummy224 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy221 f))
          (Class.cv (nb068AlphaDummy222 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy221 f)) (Class.cv (nb068AlphaDummy222 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_225`. -/
@[expose]
noncomputable def nb068AlphaDummy225 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_226`. -/
@[expose]
noncomputable def nb068AlphaDummy226 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy221 f))).fv ∪
      ((Class.cv (nb068AlphaDummy222 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_227`. -/
@[expose]
noncomputable def nb068AlphaDummy227 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy218)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy219)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_228`. -/
@[expose]
noncomputable def nb068AlphaDummy228 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy221 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy222 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_229`. -/
@[expose]
noncomputable def nb068AlphaDummy229 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy218))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_230`. -/
@[expose]
noncomputable def nb068AlphaDummy230 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy221 f))).fv ∪
      ((Class.cv (nb068AlphaDummy221 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_231`. -/
@[expose]
noncomputable def nb068AlphaDummy231 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy219))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_232`. -/
@[expose]
noncomputable def nb068AlphaDummy232 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy222 f))).fv ∪
      ((Class.cv (nb068AlphaDummy222 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_233`. -/
@[expose]
noncomputable def nb068AlphaDummy233 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy203)
          (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
            (Wff.classEq (Class.cv (nb068AlphaDummy203))
              (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy203)
          (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
            (Wff.classEq (Class.cv (nb068AlphaDummy203))
              (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_234`. -/
@[expose]
noncomputable def nb068AlphaDummy234 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy205 f)
          (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy205 f)
          (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_235`. -/
@[expose]
noncomputable def nb068AlphaDummy235 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy204))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_236`. -/
@[expose]
noncomputable def nb068AlphaDummy236 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy206 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_237`. -/
@[expose]
noncomputable def nb068AlphaDummy237 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy204)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy204)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_238`. -/
@[expose]
noncomputable def nb068AlphaDummy238 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy206 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy206 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_239`. -/
@[expose]
noncomputable def nb068AlphaDummy239 : Var :=
  (freshVar (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_240`. -/
@[expose]
noncomputable def nb068AlphaDummy240 : Var :=
  (freshVar (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_241`. -/
@[expose]
noncomputable def nb068AlphaDummy241 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_242`. -/
@[expose]
noncomputable def nb068AlphaDummy242 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_243`. -/
@[expose]
noncomputable def nb068AlphaDummy243 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_244`. -/
@[expose]
noncomputable def nb068AlphaDummy244 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_245`. -/
@[expose]
noncomputable def nb068AlphaDummy245 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy242 f))).fv ∪
      ((Class.cv (nb068AlphaDummy241 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_246`. -/
@[expose]
noncomputable def nb068AlphaDummy246 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy242 f))).fv ∪
      ((Class.cv (nb068AlphaDummy241 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_247`. -/
@[expose]
noncomputable def nb068AlphaDummy247 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCphi (Class.cv (nb068AlphaDummy244)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_248`. -/
@[expose]
noncomputable def nb068AlphaDummy248 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCphi (Class.cv (nb068AlphaDummy246 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_249`. -/
@[expose]
noncomputable def nb068AlphaDummy249 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy243)
          (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
            (Wff.classEq (Class.cv (nb068AlphaDummy243))
              (synCphi (Class.cv (nb068AlphaDummy244))))))).fv ∪
      ((Class.cab (nb068AlphaDummy243)
          (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
            (Wff.classEq (Class.cv (nb068AlphaDummy243))
              (synCphi (Class.cv (nb068AlphaDummy244))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_250`. -/
@[expose]
noncomputable def nb068AlphaDummy250 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy245 f)
          (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
              (synCphi (Class.cv (nb068AlphaDummy246 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy245 f)
          (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
              (synCphi (Class.cv (nb068AlphaDummy246 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_251`. -/
@[expose]
noncomputable def nb068AlphaDummy251 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy244))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_252`. -/
@[expose]
noncomputable def nb068AlphaDummy252 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy244))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_253`. -/
@[expose]
noncomputable def nb068AlphaDummy253 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy246 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_254`. -/
@[expose]
noncomputable def nb068AlphaDummy254 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy246 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_255`. -/
@[expose]
noncomputable def nb068AlphaDummy255 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy251)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy251)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy251))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_256`. -/
@[expose]
noncomputable def nb068AlphaDummy256 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy253 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy253 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy253 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_257`. -/
@[expose]
noncomputable def nb068AlphaDummy257 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_258`. -/
@[expose]
noncomputable def nb068AlphaDummy258 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_259`. -/
@[expose]
noncomputable def nb068AlphaDummy259 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_260`. -/
@[expose]
noncomputable def nb068AlphaDummy260 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_261`. -/
@[expose]
noncomputable def nb068AlphaDummy261 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_262`. -/
@[expose]
noncomputable def nb068AlphaDummy262 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_263`. -/
@[expose]
noncomputable def nb068AlphaDummy263 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy258))
          (Class.cv (nb068AlphaDummy259)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_264`. -/
@[expose]
noncomputable def nb068AlphaDummy264 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy261 f))
          (Class.cv (nb068AlphaDummy262 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy261 f)) (Class.cv (nb068AlphaDummy262 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_265`. -/
@[expose]
noncomputable def nb068AlphaDummy265 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_266`. -/
@[expose]
noncomputable def nb068AlphaDummy266 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy261 f))).fv ∪
      ((Class.cv (nb068AlphaDummy262 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_267`. -/
@[expose]
noncomputable def nb068AlphaDummy267 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy258)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy259)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_268`. -/
@[expose]
noncomputable def nb068AlphaDummy268 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy261 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy262 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_269`. -/
@[expose]
noncomputable def nb068AlphaDummy269 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy258))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_270`. -/
@[expose]
noncomputable def nb068AlphaDummy270 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy261 f))).fv ∪
      ((Class.cv (nb068AlphaDummy261 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_271`. -/
@[expose]
noncomputable def nb068AlphaDummy271 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy259))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_272`. -/
@[expose]
noncomputable def nb068AlphaDummy272 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy262 f))).fv ∪
      ((Class.cv (nb068AlphaDummy262 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_273`. -/
@[expose]
noncomputable def nb068AlphaDummy273 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy243)
          (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
            (Wff.classEq (Class.cv (nb068AlphaDummy243))
              (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy243)
          (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
            (Wff.classEq (Class.cv (nb068AlphaDummy243))
              (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_274`. -/
@[expose]
noncomputable def nb068AlphaDummy274 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy245 f)
          (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy245 f)
          (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_275`. -/
@[expose]
noncomputable def nb068AlphaDummy275 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy244))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_276`. -/
@[expose]
noncomputable def nb068AlphaDummy276 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy246 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_277`. -/
@[expose]
noncomputable def nb068AlphaDummy277 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy244)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy244)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_278`. -/
@[expose]
noncomputable def nb068AlphaDummy278 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy246 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy246 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_279`. -/
@[expose]
noncomputable def nb068AlphaDummy279 : Var :=
  (freshVar (((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
          (Class.cv (nb068AlphaDummy002)))).fv ∪
      ((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
          (Class.cv (nb068AlphaDummy002)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_280`. -/
@[expose]
noncomputable def nb068AlphaDummy280 (y : Var) (f : Var) : Var :=
  (freshVar (((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv ∪
      ((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_281`. -/
@[expose]
noncomputable def nb068AlphaDummy281 : Var :=
  (freshVar (((synCrn (Class.cv (nb068AlphaDummy000)))).fv ∪
      ((Class.cv (nb068AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_282`. -/
@[expose]
noncomputable def nb068AlphaDummy282 (y : Var) (f : Var) : Var :=
  (freshVar (((synCrn (Class.cv f))).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_283`. -/
@[expose]
noncomputable def nb068AlphaDummy283 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_284`. -/
@[expose]
noncomputable def nb068AlphaDummy284 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_285`. -/
@[expose]
noncomputable def nb068AlphaDummy285 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_286`. -/
@[expose]
noncomputable def nb068AlphaDummy286 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_287`. -/
@[expose]
noncomputable def nb068AlphaDummy287 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_288`. -/
@[expose]
noncomputable def nb068AlphaDummy288 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_289`. -/
@[expose]
noncomputable def nb068AlphaDummy289 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy286 f))).fv ∪
      ((Class.cv (nb068AlphaDummy285 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_290`. -/
@[expose]
noncomputable def nb068AlphaDummy290 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy286 f))).fv ∪
      ((Class.cv (nb068AlphaDummy285 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_291`. -/
@[expose]
noncomputable def nb068AlphaDummy291 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCphi (Class.cv (nb068AlphaDummy288)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_292`. -/
@[expose]
noncomputable def nb068AlphaDummy292 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCphi (Class.cv (nb068AlphaDummy290 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_293`. -/
@[expose]
noncomputable def nb068AlphaDummy293 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy287)
          (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
            (Wff.classEq (Class.cv (nb068AlphaDummy287))
              (synCphi (Class.cv (nb068AlphaDummy288))))))).fv ∪
      ((Class.cab (nb068AlphaDummy287)
          (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
            (Wff.classEq (Class.cv (nb068AlphaDummy287))
              (synCphi (Class.cv (nb068AlphaDummy288))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_294`. -/
@[expose]
noncomputable def nb068AlphaDummy294 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy289 f)
          (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
              (synCphi (Class.cv (nb068AlphaDummy290 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy289 f)
          (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
              (synCphi (Class.cv (nb068AlphaDummy290 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_295`. -/
@[expose]
noncomputable def nb068AlphaDummy295 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy288))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_296`. -/
@[expose]
noncomputable def nb068AlphaDummy296 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy288))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_297`. -/
@[expose]
noncomputable def nb068AlphaDummy297 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy290 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_298`. -/
@[expose]
noncomputable def nb068AlphaDummy298 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy290 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_299`. -/
@[expose]
noncomputable def nb068AlphaDummy299 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy295)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy295)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy295))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_300`. -/
@[expose]
noncomputable def nb068AlphaDummy300 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy297 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy297 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy297 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_301`. -/
@[expose]
noncomputable def nb068AlphaDummy301 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_302`. -/
@[expose]
noncomputable def nb068AlphaDummy302 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_303`. -/
@[expose]
noncomputable def nb068AlphaDummy303 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_304`. -/
@[expose]
noncomputable def nb068AlphaDummy304 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_305`. -/
@[expose]
noncomputable def nb068AlphaDummy305 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_306`. -/
@[expose]
noncomputable def nb068AlphaDummy306 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_307`. -/
@[expose]
noncomputable def nb068AlphaDummy307 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy302))
          (Class.cv (nb068AlphaDummy303)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_308`. -/
@[expose]
noncomputable def nb068AlphaDummy308 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy305 f))
          (Class.cv (nb068AlphaDummy306 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy305 f)) (Class.cv (nb068AlphaDummy306 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_309`. -/
@[expose]
noncomputable def nb068AlphaDummy309 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_310`. -/
@[expose]
noncomputable def nb068AlphaDummy310 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy305 f))).fv ∪
      ((Class.cv (nb068AlphaDummy306 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_311`. -/
@[expose]
noncomputable def nb068AlphaDummy311 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy302)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy303)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_312`. -/
@[expose]
noncomputable def nb068AlphaDummy312 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy305 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy306 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_313`. -/
@[expose]
noncomputable def nb068AlphaDummy313 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy302))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_314`. -/
@[expose]
noncomputable def nb068AlphaDummy314 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy305 f))).fv ∪
      ((Class.cv (nb068AlphaDummy305 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_315`. -/
@[expose]
noncomputable def nb068AlphaDummy315 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy303))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_316`. -/
@[expose]
noncomputable def nb068AlphaDummy316 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy306 f))).fv ∪
      ((Class.cv (nb068AlphaDummy306 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_317`. -/
@[expose]
noncomputable def nb068AlphaDummy317 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy287)
          (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
            (Wff.classEq (Class.cv (nb068AlphaDummy287))
              (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy287)
          (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
            (Wff.classEq (Class.cv (nb068AlphaDummy287))
              (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_318`. -/
@[expose]
noncomputable def nb068AlphaDummy318 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy289 f)
          (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy289 f)
          (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_319`. -/
@[expose]
noncomputable def nb068AlphaDummy319 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy288))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_320`. -/
@[expose]
noncomputable def nb068AlphaDummy320 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy290 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_321`. -/
@[expose]
noncomputable def nb068AlphaDummy321 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy288)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy288)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_322`. -/
@[expose]
noncomputable def nb068AlphaDummy322 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy290 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy290 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_323`. -/
@[expose]
noncomputable def nb068AlphaDummy323 : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
            (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))) (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
            (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_324`. -/
@[expose]
noncomputable def nb068AlphaDummy324 (f : Var) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
          (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
          (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_325`. -/
@[expose]
noncomputable def nb068AlphaDummy325 : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
          (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000)))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_326`. -/
@[expose]
noncomputable def nb068AlphaDummy326 (f : Var) : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))).fv ∪
      ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_327`. -/
@[expose]
noncomputable def nb068AlphaDummy327 : Var :=
  (freshVar (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_328`. -/
@[expose]
noncomputable def nb068AlphaDummy328 : Var :=
  (freshVar (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_329`. -/
@[expose]
noncomputable def nb068AlphaDummy329 : Var :=
  (freshVar (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_330`. -/
@[expose]
noncomputable def nb068AlphaDummy330 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_331`. -/
@[expose]
noncomputable def nb068AlphaDummy331 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_332`. -/
@[expose]
noncomputable def nb068AlphaDummy332 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_333`. -/
@[expose]
noncomputable def nb068AlphaDummy333 : Var :=
  (freshVar
    (({(nb068AlphaDummy327)} : Finset Var) ∪ ({(nb068AlphaDummy328)} : Finset Var) ∪
      ((synWex (nb068AlphaDummy329) (synWa (synWbr (Class.cv (nb068AlphaDummy327))
              (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))
              (Class.cv (nb068AlphaDummy329))) (synWbr (Class.cv (nb068AlphaDummy329))
              (synCcnv (Class.cv (nb068AlphaDummy000)))
              (Class.cv (nb068AlphaDummy328)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_334`. -/
@[expose]
noncomputable def nb068AlphaDummy334 (f : Var) : Var :=
  (freshVar (({(nb068AlphaDummy330 f)} : Finset Var) ∪
        ({(nb068AlphaDummy331 f)} : Finset Var) ∪ ((synWex (nb068AlphaDummy332 f) (synWa
            (synWbr (Class.cv (nb068AlphaDummy330 f))
              (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb068AlphaDummy332 f)))
            (synWbr (Class.cv (nb068AlphaDummy332 f)) (synCcnv (Class.cv f))
              (Class.cv (nb068AlphaDummy331 f)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_335`. -/
@[expose]
noncomputable def nb068AlphaDummy335 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_336`. -/
@[expose]
noncomputable def nb068AlphaDummy336 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_337`. -/
@[expose]
noncomputable def nb068AlphaDummy337 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy330 f))).fv ∪
      ((Class.cv (nb068AlphaDummy331 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_338`. -/
@[expose]
noncomputable def nb068AlphaDummy338 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy330 f))).fv ∪
      ((Class.cv (nb068AlphaDummy331 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_339`. -/
@[expose]
noncomputable def nb068AlphaDummy339 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCphi (Class.cv (nb068AlphaDummy336)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_340`. -/
@[expose]
noncomputable def nb068AlphaDummy340 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCphi (Class.cv (nb068AlphaDummy338 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_341`. -/
@[expose]
noncomputable def nb068AlphaDummy341 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy335)
          (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
            (Wff.classEq (Class.cv (nb068AlphaDummy335))
              (synCphi (Class.cv (nb068AlphaDummy336))))))).fv ∪
      ((Class.cab (nb068AlphaDummy335)
          (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
            (Wff.classEq (Class.cv (nb068AlphaDummy335))
              (synCphi (Class.cv (nb068AlphaDummy336))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_342`. -/
@[expose]
noncomputable def nb068AlphaDummy342 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy337 f)
          (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
              (synCphi (Class.cv (nb068AlphaDummy338 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy337 f)
          (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
              (synCphi (Class.cv (nb068AlphaDummy338 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_343`. -/
@[expose]
noncomputable def nb068AlphaDummy343 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy336))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_344`. -/
@[expose]
noncomputable def nb068AlphaDummy344 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy336))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_345`. -/
@[expose]
noncomputable def nb068AlphaDummy345 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy338 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_346`. -/
@[expose]
noncomputable def nb068AlphaDummy346 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy338 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_347`. -/
@[expose]
noncomputable def nb068AlphaDummy347 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy343)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy343)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy343))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_348`. -/
@[expose]
noncomputable def nb068AlphaDummy348 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy345 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy345 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy345 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_349`. -/
@[expose]
noncomputable def nb068AlphaDummy349 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_350`. -/
@[expose]
noncomputable def nb068AlphaDummy350 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_351`. -/
@[expose]
noncomputable def nb068AlphaDummy351 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_352`. -/
@[expose]
noncomputable def nb068AlphaDummy352 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_353`. -/
@[expose]
noncomputable def nb068AlphaDummy353 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_354`. -/
@[expose]
noncomputable def nb068AlphaDummy354 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_355`. -/
@[expose]
noncomputable def nb068AlphaDummy355 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy350))
          (Class.cv (nb068AlphaDummy351)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_356`. -/
@[expose]
noncomputable def nb068AlphaDummy356 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy353 f))
          (Class.cv (nb068AlphaDummy354 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy353 f)) (Class.cv (nb068AlphaDummy354 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_357`. -/
@[expose]
noncomputable def nb068AlphaDummy357 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_358`. -/
@[expose]
noncomputable def nb068AlphaDummy358 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy353 f))).fv ∪
      ((Class.cv (nb068AlphaDummy354 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_359`. -/
@[expose]
noncomputable def nb068AlphaDummy359 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy350)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy351)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_360`. -/
@[expose]
noncomputable def nb068AlphaDummy360 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy353 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy354 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_361`. -/
@[expose]
noncomputable def nb068AlphaDummy361 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy350))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_362`. -/
@[expose]
noncomputable def nb068AlphaDummy362 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy353 f))).fv ∪
      ((Class.cv (nb068AlphaDummy353 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_363`. -/
@[expose]
noncomputable def nb068AlphaDummy363 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy351))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_364`. -/
@[expose]
noncomputable def nb068AlphaDummy364 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy354 f))).fv ∪
      ((Class.cv (nb068AlphaDummy354 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_365`. -/
@[expose]
noncomputable def nb068AlphaDummy365 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy335)
          (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
            (Wff.classEq (Class.cv (nb068AlphaDummy335))
              (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy335)
          (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
            (Wff.classEq (Class.cv (nb068AlphaDummy335))
              (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_366`. -/
@[expose]
noncomputable def nb068AlphaDummy366 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy337 f)
          (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy337 f)
          (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_367`. -/
@[expose]
noncomputable def nb068AlphaDummy367 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy336))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_368`. -/
@[expose]
noncomputable def nb068AlphaDummy368 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy338 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_369`. -/
@[expose]
noncomputable def nb068AlphaDummy369 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy336)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy336)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_370`. -/
@[expose]
noncomputable def nb068AlphaDummy370 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy338 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy338 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_371`. -/
@[expose]
noncomputable def nb068AlphaDummy371 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_372`. -/
@[expose]
noncomputable def nb068AlphaDummy372 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_373`. -/
@[expose]
noncomputable def nb068AlphaDummy373 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy330 f))).fv ∪
      ((Class.cv (nb068AlphaDummy332 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_374`. -/
@[expose]
noncomputable def nb068AlphaDummy374 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy330 f))).fv ∪
      ((Class.cv (nb068AlphaDummy332 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_375`. -/
@[expose]
noncomputable def nb068AlphaDummy375 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCphi (Class.cv (nb068AlphaDummy372)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_376`. -/
@[expose]
noncomputable def nb068AlphaDummy376 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCphi (Class.cv (nb068AlphaDummy374 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_377`. -/
@[expose]
noncomputable def nb068AlphaDummy377 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy371)
          (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
            (Wff.classEq (Class.cv (nb068AlphaDummy371))
              (synCphi (Class.cv (nb068AlphaDummy372))))))).fv ∪
      ((Class.cab (nb068AlphaDummy371)
          (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
            (Wff.classEq (Class.cv (nb068AlphaDummy371))
              (synCphi (Class.cv (nb068AlphaDummy372))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_378`. -/
@[expose]
noncomputable def nb068AlphaDummy378 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy373 f)
          (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
              (synCphi (Class.cv (nb068AlphaDummy374 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy373 f)
          (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
              (synCphi (Class.cv (nb068AlphaDummy374 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_379`. -/
@[expose]
noncomputable def nb068AlphaDummy379 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy372))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_380`. -/
@[expose]
noncomputable def nb068AlphaDummy380 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy372))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_381`. -/
@[expose]
noncomputable def nb068AlphaDummy381 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy374 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_382`. -/
@[expose]
noncomputable def nb068AlphaDummy382 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy374 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_383`. -/
@[expose]
noncomputable def nb068AlphaDummy383 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy379)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy379)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy379))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_384`. -/
@[expose]
noncomputable def nb068AlphaDummy384 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy381 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy381 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy381 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_385`. -/
@[expose]
noncomputable def nb068AlphaDummy385 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_386`. -/
@[expose]
noncomputable def nb068AlphaDummy386 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_387`. -/
@[expose]
noncomputable def nb068AlphaDummy387 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_388`. -/
@[expose]
noncomputable def nb068AlphaDummy388 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_389`. -/
@[expose]
noncomputable def nb068AlphaDummy389 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_390`. -/
@[expose]
noncomputable def nb068AlphaDummy390 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_391`. -/
@[expose]
noncomputable def nb068AlphaDummy391 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy386))
          (Class.cv (nb068AlphaDummy387)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_392`. -/
@[expose]
noncomputable def nb068AlphaDummy392 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy389 f))
          (Class.cv (nb068AlphaDummy390 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy389 f)) (Class.cv (nb068AlphaDummy390 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_393`. -/
@[expose]
noncomputable def nb068AlphaDummy393 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_394`. -/
@[expose]
noncomputable def nb068AlphaDummy394 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy389 f))).fv ∪
      ((Class.cv (nb068AlphaDummy390 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_395`. -/
@[expose]
noncomputable def nb068AlphaDummy395 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy386)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy387)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_396`. -/
@[expose]
noncomputable def nb068AlphaDummy396 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy389 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy390 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_397`. -/
@[expose]
noncomputable def nb068AlphaDummy397 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy386))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_398`. -/
@[expose]
noncomputable def nb068AlphaDummy398 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy389 f))).fv ∪
      ((Class.cv (nb068AlphaDummy389 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_399`. -/
@[expose]
noncomputable def nb068AlphaDummy399 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy387))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_400`. -/
@[expose]
noncomputable def nb068AlphaDummy400 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy390 f))).fv ∪
      ((Class.cv (nb068AlphaDummy390 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_401`. -/
@[expose]
noncomputable def nb068AlphaDummy401 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy371)
          (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
            (Wff.classEq (Class.cv (nb068AlphaDummy371))
              (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy371)
          (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
            (Wff.classEq (Class.cv (nb068AlphaDummy371))
              (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_402`. -/
@[expose]
noncomputable def nb068AlphaDummy402 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy373 f)
          (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy373 f)
          (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_403`. -/
@[expose]
noncomputable def nb068AlphaDummy403 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy372))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_404`. -/
@[expose]
noncomputable def nb068AlphaDummy404 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy374 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_405`. -/
@[expose]
noncomputable def nb068AlphaDummy405 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy372)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy372)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_406`. -/
@[expose]
noncomputable def nb068AlphaDummy406 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy374 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy374 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_407`. -/
@[expose]
noncomputable def nb068AlphaDummy407 : Var :=
  (freshVar (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_408`. -/
@[expose]
noncomputable def nb068AlphaDummy408 : Var :=
  (freshVar (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_409`. -/
@[expose]
noncomputable def nb068AlphaDummy409 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_410`. -/
@[expose]
noncomputable def nb068AlphaDummy410 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_411`. -/
@[expose]
noncomputable def nb068AlphaDummy411 : Var :=
  (freshVar
    (({(nb068AlphaDummy407)} : Finset Var) ∪ ({(nb068AlphaDummy408)} : Finset Var) ∪
      ((synWbr (Class.cv (nb068AlphaDummy408)) (synCcnv (Class.cv (nb068AlphaDummy000)))
          (Class.cv (nb068AlphaDummy407)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_412`. -/
@[expose]
noncomputable def nb068AlphaDummy412 (f : Var) : Var :=
  (freshVar (({(nb068AlphaDummy409 f)} : Finset Var) ∪
        ({(nb068AlphaDummy410 f)} : Finset Var) ∪
      ((synWbr (Class.cv (nb068AlphaDummy410 f)) (synCcnv (Class.cv f))
          (Class.cv (nb068AlphaDummy409 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_413`. -/
@[expose]
noncomputable def nb068AlphaDummy413 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_414`. -/
@[expose]
noncomputable def nb068AlphaDummy414 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_415`. -/
@[expose]
noncomputable def nb068AlphaDummy415 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy409 f))).fv ∪
      ((Class.cv (nb068AlphaDummy410 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_416`. -/
@[expose]
noncomputable def nb068AlphaDummy416 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy409 f))).fv ∪
      ((Class.cv (nb068AlphaDummy410 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_417`. -/
@[expose]
noncomputable def nb068AlphaDummy417 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCphi (Class.cv (nb068AlphaDummy414)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_418`. -/
@[expose]
noncomputable def nb068AlphaDummy418 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCphi (Class.cv (nb068AlphaDummy416 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_419`. -/
@[expose]
noncomputable def nb068AlphaDummy419 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy413)
          (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
            (Wff.classEq (Class.cv (nb068AlphaDummy413))
              (synCphi (Class.cv (nb068AlphaDummy414))))))).fv ∪
      ((Class.cab (nb068AlphaDummy413)
          (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
            (Wff.classEq (Class.cv (nb068AlphaDummy413))
              (synCphi (Class.cv (nb068AlphaDummy414))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_420`. -/
@[expose]
noncomputable def nb068AlphaDummy420 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy415 f)
          (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
              (synCphi (Class.cv (nb068AlphaDummy416 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy415 f)
          (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
              (synCphi (Class.cv (nb068AlphaDummy416 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_421`. -/
@[expose]
noncomputable def nb068AlphaDummy421 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy414))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_422`. -/
@[expose]
noncomputable def nb068AlphaDummy422 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy414))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_423`. -/
@[expose]
noncomputable def nb068AlphaDummy423 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy416 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_424`. -/
@[expose]
noncomputable def nb068AlphaDummy424 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy416 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_425`. -/
@[expose]
noncomputable def nb068AlphaDummy425 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy421)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy421)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy421))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_426`. -/
@[expose]
noncomputable def nb068AlphaDummy426 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy423 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy423 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy423 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_427`. -/
@[expose]
noncomputable def nb068AlphaDummy427 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_428`. -/
@[expose]
noncomputable def nb068AlphaDummy428 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_429`. -/
@[expose]
noncomputable def nb068AlphaDummy429 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_430`. -/
@[expose]
noncomputable def nb068AlphaDummy430 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_431`. -/
@[expose]
noncomputable def nb068AlphaDummy431 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_432`. -/
@[expose]
noncomputable def nb068AlphaDummy432 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_433`. -/
@[expose]
noncomputable def nb068AlphaDummy433 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy428))
          (Class.cv (nb068AlphaDummy429)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_434`. -/
@[expose]
noncomputable def nb068AlphaDummy434 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy431 f))
          (Class.cv (nb068AlphaDummy432 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy431 f)) (Class.cv (nb068AlphaDummy432 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_435`. -/
@[expose]
noncomputable def nb068AlphaDummy435 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_436`. -/
@[expose]
noncomputable def nb068AlphaDummy436 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy431 f))).fv ∪
      ((Class.cv (nb068AlphaDummy432 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_437`. -/
@[expose]
noncomputable def nb068AlphaDummy437 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy428)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy429)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_438`. -/
@[expose]
noncomputable def nb068AlphaDummy438 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy431 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy432 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_439`. -/
@[expose]
noncomputable def nb068AlphaDummy439 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy428))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_440`. -/
@[expose]
noncomputable def nb068AlphaDummy440 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy431 f))).fv ∪
      ((Class.cv (nb068AlphaDummy431 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_441`. -/
@[expose]
noncomputable def nb068AlphaDummy441 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy429))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_442`. -/
@[expose]
noncomputable def nb068AlphaDummy442 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy432 f))).fv ∪
      ((Class.cv (nb068AlphaDummy432 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_443`. -/
@[expose]
noncomputable def nb068AlphaDummy443 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy413)
          (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
            (Wff.classEq (Class.cv (nb068AlphaDummy413))
              (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy413)
          (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
            (Wff.classEq (Class.cv (nb068AlphaDummy413))
              (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_444`. -/
@[expose]
noncomputable def nb068AlphaDummy444 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy415 f)
          (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy415 f)
          (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_445`. -/
@[expose]
noncomputable def nb068AlphaDummy445 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy414))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_446`. -/
@[expose]
noncomputable def nb068AlphaDummy446 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy416 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_447`. -/
@[expose]
noncomputable def nb068AlphaDummy447 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy414)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy414)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_448`. -/
@[expose]
noncomputable def nb068AlphaDummy448 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy416 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy416 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_449`. -/
@[expose]
noncomputable def nb068AlphaDummy449 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_450`. -/
@[expose]
noncomputable def nb068AlphaDummy450 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_451`. -/
@[expose]
noncomputable def nb068AlphaDummy451 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy410 f))).fv ∪
      ((Class.cv (nb068AlphaDummy409 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_452`. -/
@[expose]
noncomputable def nb068AlphaDummy452 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy410 f))).fv ∪
      ((Class.cv (nb068AlphaDummy409 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_453`. -/
@[expose]
noncomputable def nb068AlphaDummy453 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCphi (Class.cv (nb068AlphaDummy450)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_454`. -/
@[expose]
noncomputable def nb068AlphaDummy454 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCphi (Class.cv (nb068AlphaDummy452 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_455`. -/
@[expose]
noncomputable def nb068AlphaDummy455 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy449)
          (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
            (Wff.classEq (Class.cv (nb068AlphaDummy449))
              (synCphi (Class.cv (nb068AlphaDummy450))))))).fv ∪
      ((Class.cab (nb068AlphaDummy449)
          (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
            (Wff.classEq (Class.cv (nb068AlphaDummy449))
              (synCphi (Class.cv (nb068AlphaDummy450))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_456`. -/
@[expose]
noncomputable def nb068AlphaDummy456 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy451 f)
          (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
              (synCphi (Class.cv (nb068AlphaDummy452 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy451 f)
          (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
              (synCphi (Class.cv (nb068AlphaDummy452 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_457`. -/
@[expose]
noncomputable def nb068AlphaDummy457 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy450))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_458`. -/
@[expose]
noncomputable def nb068AlphaDummy458 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy450))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_459`. -/
@[expose]
noncomputable def nb068AlphaDummy459 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy452 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_460`. -/
@[expose]
noncomputable def nb068AlphaDummy460 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy452 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_461`. -/
@[expose]
noncomputable def nb068AlphaDummy461 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy457)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy457))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_462`. -/
@[expose]
noncomputable def nb068AlphaDummy462 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy459 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy459 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_463`. -/
@[expose]
noncomputable def nb068AlphaDummy463 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_464`. -/
@[expose]
noncomputable def nb068AlphaDummy464 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_465`. -/
@[expose]
noncomputable def nb068AlphaDummy465 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_466`. -/
@[expose]
noncomputable def nb068AlphaDummy466 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_467`. -/
@[expose]
noncomputable def nb068AlphaDummy467 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_468`. -/
@[expose]
noncomputable def nb068AlphaDummy468 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_469`. -/
@[expose]
noncomputable def nb068AlphaDummy469 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy464))
          (Class.cv (nb068AlphaDummy465)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_470`. -/
@[expose]
noncomputable def nb068AlphaDummy470 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy467 f))
          (Class.cv (nb068AlphaDummy468 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy467 f)) (Class.cv (nb068AlphaDummy468 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_471`. -/
@[expose]
noncomputable def nb068AlphaDummy471 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_472`. -/
@[expose]
noncomputable def nb068AlphaDummy472 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy467 f))).fv ∪
      ((Class.cv (nb068AlphaDummy468 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_473`. -/
@[expose]
noncomputable def nb068AlphaDummy473 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy464)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy465)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_474`. -/
@[expose]
noncomputable def nb068AlphaDummy474 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy467 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy468 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_475`. -/
@[expose]
noncomputable def nb068AlphaDummy475 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy464))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_476`. -/
@[expose]
noncomputable def nb068AlphaDummy476 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy467 f))).fv ∪
      ((Class.cv (nb068AlphaDummy467 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_477`. -/
@[expose]
noncomputable def nb068AlphaDummy477 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy465))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_478`. -/
@[expose]
noncomputable def nb068AlphaDummy478 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy468 f))).fv ∪
      ((Class.cv (nb068AlphaDummy468 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_479`. -/
@[expose]
noncomputable def nb068AlphaDummy479 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy449)
          (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
            (Wff.classEq (Class.cv (nb068AlphaDummy449))
              (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy449)
          (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
            (Wff.classEq (Class.cv (nb068AlphaDummy449))
              (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_480`. -/
@[expose]
noncomputable def nb068AlphaDummy480 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy451 f)
          (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy451 f)
          (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_481`. -/
@[expose]
noncomputable def nb068AlphaDummy481 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy450))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_482`. -/
@[expose]
noncomputable def nb068AlphaDummy482 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy452 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_483`. -/
@[expose]
noncomputable def nb068AlphaDummy483 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy450)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy450)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_484`. -/
@[expose]
noncomputable def nb068AlphaDummy484 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy452 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy452 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_485`. -/
@[expose]
noncomputable def nb068AlphaDummy485 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_486`. -/
@[expose]
noncomputable def nb068AlphaDummy486 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_487`. -/
@[expose]
noncomputable def nb068AlphaDummy487 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy332 f))).fv ∪
      ((Class.cv (nb068AlphaDummy331 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_488`. -/
@[expose]
noncomputable def nb068AlphaDummy488 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy332 f))).fv ∪
      ((Class.cv (nb068AlphaDummy331 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_489`. -/
@[expose]
noncomputable def nb068AlphaDummy489 : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCphi (Class.cv (nb068AlphaDummy486)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_490`. -/
@[expose]
noncomputable def nb068AlphaDummy490 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCphi (Class.cv (nb068AlphaDummy488 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_491`. -/
@[expose]
noncomputable def nb068AlphaDummy491 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy485)
          (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
            (Wff.classEq (Class.cv (nb068AlphaDummy485))
              (synCphi (Class.cv (nb068AlphaDummy486))))))).fv ∪
      ((Class.cab (nb068AlphaDummy485)
          (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
            (Wff.classEq (Class.cv (nb068AlphaDummy485))
              (synCphi (Class.cv (nb068AlphaDummy486))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_492`. -/
@[expose]
noncomputable def nb068AlphaDummy492 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy487 f)
          (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
              (synCphi (Class.cv (nb068AlphaDummy488 f))))))).fv ∪
      ((Class.cab (nb068AlphaDummy487 f)
          (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
              (synCphi (Class.cv (nb068AlphaDummy488 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_493`. -/
@[expose]
noncomputable def nb068AlphaDummy493 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy486))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_494`. -/
@[expose]
noncomputable def nb068AlphaDummy494 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy486))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_495`. -/
@[expose]
noncomputable def nb068AlphaDummy495 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy488 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_496`. -/
@[expose]
noncomputable def nb068AlphaDummy496 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy488 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_497`. -/
@[expose]
noncomputable def nb068AlphaDummy497 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy493)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy493)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy493))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_498`. -/
@[expose]
noncomputable def nb068AlphaDummy498 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb068AlphaDummy495 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb068AlphaDummy495 f)) (synC1c))).fv ∪
      ((Class.cv (nb068AlphaDummy495 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_499`. -/
@[expose]
noncomputable def nb068AlphaDummy499 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_500`. -/
@[expose]
noncomputable def nb068AlphaDummy500 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_501`. -/
@[expose]
noncomputable def nb068AlphaDummy501 : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_502`. -/
@[expose]
noncomputable def nb068AlphaDummy502 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_503`. -/
@[expose]
noncomputable def nb068AlphaDummy503 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_504`. -/
@[expose]
noncomputable def nb068AlphaDummy504 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_505`. -/
@[expose]
noncomputable def nb068AlphaDummy505 : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy500))
          (Class.cv (nb068AlphaDummy501)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_506`. -/
@[expose]
noncomputable def nb068AlphaDummy506 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb068AlphaDummy503 f))
          (Class.cv (nb068AlphaDummy504 f)))).fv ∪
      ((synCnin (Class.cv (nb068AlphaDummy503 f)) (Class.cv (nb068AlphaDummy504 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_507`. -/
@[expose]
noncomputable def nb068AlphaDummy507 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_508`. -/
@[expose]
noncomputable def nb068AlphaDummy508 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy503 f))).fv ∪
      ((Class.cv (nb068AlphaDummy504 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_509`. -/
@[expose]
noncomputable def nb068AlphaDummy509 : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy500)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy501)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_510`. -/
@[expose]
noncomputable def nb068AlphaDummy510 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb068AlphaDummy503 f)))).fv ∪
      ((synCcompl (Class.cv (nb068AlphaDummy504 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_511`. -/
@[expose]
noncomputable def nb068AlphaDummy511 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy500))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_512`. -/
@[expose]
noncomputable def nb068AlphaDummy512 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy503 f))).fv ∪
      ((Class.cv (nb068AlphaDummy503 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_513`. -/
@[expose]
noncomputable def nb068AlphaDummy513 : Var :=
  (freshVar
    (((Class.cv (nb068AlphaDummy501))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_514`. -/
@[expose]
noncomputable def nb068AlphaDummy514 (f : Var) : Var :=
  (freshVar (((Class.cv (nb068AlphaDummy504 f))).fv ∪
      ((Class.cv (nb068AlphaDummy504 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_515`. -/
@[expose]
noncomputable def nb068AlphaDummy515 : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy485)
          (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
            (Wff.classEq (Class.cv (nb068AlphaDummy485))
              (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy485)
          (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
            (Wff.classEq (Class.cv (nb068AlphaDummy485))
              (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_516`. -/
@[expose]
noncomputable def nb068AlphaDummy516 (f : Var) : Var :=
  (freshVar (((Class.cab (nb068AlphaDummy487 f)
          (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy487 f)
          (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
            (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
              (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_517`. -/
@[expose]
noncomputable def nb068AlphaDummy517 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy486))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_518`. -/
@[expose]
noncomputable def nb068AlphaDummy518 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb068AlphaDummy488 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_519`. -/
@[expose]
noncomputable def nb068AlphaDummy519 : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy486)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy486)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb068_alpha_dummy_520`. -/
@[expose]
noncomputable def nb068AlphaDummy520 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb068AlphaDummy488 f)))).fv ∪
      ((synCphi (Class.cv (nb068AlphaDummy488 f)))).fv) 0)

theorem nb068_fresh_000 :
    (nb068AlphaDummy011) ∉
      (((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCphi (Class.cv (nb068AlphaDummy006))))))).fv ∪
        ((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCphi (Class.cv (nb068AlphaDummy006))))))).fv) :=
  by
  simpa only [nb068AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCphi (Class.cv (nb068AlphaDummy006))))))).fv ∪
        ((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCphi (Class.cv (nb068AlphaDummy006))))))).fv)
      0

theorem nb068_fresh_001 :
    (nb068AlphaDummy035) ∉
      (((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_002 (x : Var) (y : Var) :
    (nb068AlphaDummy012 x y) ∉
      (((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCphi (Class.cv (nb068AlphaDummy008 x y))))))).fv ∪
        ((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCphi (Class.cv (nb068AlphaDummy008 x y))))))).fv) :=
  by
  simpa only [nb068AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCphi (Class.cv (nb068AlphaDummy008 x y))))))).fv ∪
        ((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCphi (Class.cv (nb068AlphaDummy008 x y))))))).fv)
      0

theorem nb068_fresh_003 (x : Var) (y : Var) :
    (nb068AlphaDummy036 x y) ∉
      (((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_004 :
    (nb068AlphaDummy059) ∉
      (((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCphi (Class.cv (nb068AlphaDummy054))))))).fv ∪
        ((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCphi (Class.cv (nb068AlphaDummy054))))))).fv) :=
  by
  simpa only [nb068AlphaDummy059] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCphi (Class.cv (nb068AlphaDummy054))))))).fv ∪
        ((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCphi (Class.cv (nb068AlphaDummy054))))))).fv)
      0

theorem nb068_fresh_005 :
    (nb068AlphaDummy083) ∉
      (((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy083] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_006 (f : Var) :
    (nb068AlphaDummy060 f) ∉
      (((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCphi (Class.cv (nb068AlphaDummy056 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCphi (Class.cv (nb068AlphaDummy056 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy060] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCphi (Class.cv (nb068AlphaDummy056 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCphi (Class.cv (nb068AlphaDummy056 f))))))).fv)
      0

theorem nb068_fresh_007 (f : Var) :
    (nb068AlphaDummy084 f) ∉
      (((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy084] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_008 :
    (nb068AlphaDummy095) ∉
      (((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCphi (Class.cv (nb068AlphaDummy090))))))).fv ∪
        ((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCphi (Class.cv (nb068AlphaDummy090))))))).fv) :=
  by
  simpa only [nb068AlphaDummy095] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCphi (Class.cv (nb068AlphaDummy090))))))).fv ∪
        ((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCphi (Class.cv (nb068AlphaDummy090))))))).fv)
      0

theorem nb068_fresh_009 :
    (nb068AlphaDummy119) ∉
      (((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy119] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_010 (f : Var) :
    (nb068AlphaDummy096 f) ∉
      (((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCphi (Class.cv (nb068AlphaDummy092 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCphi (Class.cv (nb068AlphaDummy092 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy096] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCphi (Class.cv (nb068AlphaDummy092 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCphi (Class.cv (nb068AlphaDummy092 f))))))).fv)
      0

theorem nb068_fresh_011 (f : Var) :
    (nb068AlphaDummy120 f) ∉
      (((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy120] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_012 :
    (nb068AlphaDummy137) ∉
      (((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCphi (Class.cv (nb068AlphaDummy132))))))).fv ∪
        ((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCphi (Class.cv (nb068AlphaDummy132))))))).fv) :=
  by
  simpa only [nb068AlphaDummy137] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCphi (Class.cv (nb068AlphaDummy132))))))).fv ∪
        ((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCphi (Class.cv (nb068AlphaDummy132))))))).fv)
      0

theorem nb068_fresh_013 :
    (nb068AlphaDummy161) ∉
      (((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy161] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_014 (f : Var) :
    (nb068AlphaDummy138 f) ∉
      (((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCphi (Class.cv (nb068AlphaDummy134 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCphi (Class.cv (nb068AlphaDummy134 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy138] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCphi (Class.cv (nb068AlphaDummy134 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCphi (Class.cv (nb068AlphaDummy134 f))))))).fv)
      0

theorem nb068_fresh_015 (f : Var) :
    (nb068AlphaDummy162 f) ∉
      (((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy162] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_016 :
    (nb068AlphaDummy197) ∉
      (((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy197] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_017 :
    (nb068AlphaDummy173) ∉
      (((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCphi (Class.cv (nb068AlphaDummy168))))))).fv ∪
        ((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCphi (Class.cv (nb068AlphaDummy168))))))).fv) :=
  by
  simpa only [nb068AlphaDummy173] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCphi (Class.cv (nb068AlphaDummy168))))))).fv ∪
        ((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCphi (Class.cv (nb068AlphaDummy168))))))).fv)
      0

theorem nb068_fresh_018 (f : Var) :
    (nb068AlphaDummy198 f) ∉
      (((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy198] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_019 (f : Var) :
    (nb068AlphaDummy174 f) ∉
      (((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCphi (Class.cv (nb068AlphaDummy170 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCphi (Class.cv (nb068AlphaDummy170 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy174] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCphi (Class.cv (nb068AlphaDummy170 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCphi (Class.cv (nb068AlphaDummy170 f))))))).fv)
      0

theorem nb068_fresh_020 :
    (nb068AlphaDummy233) ∉
      (((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy233] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_021 :
    (nb068AlphaDummy209) ∉
      (((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCphi (Class.cv (nb068AlphaDummy204))))))).fv ∪
        ((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCphi (Class.cv (nb068AlphaDummy204))))))).fv) :=
  by
  simpa only [nb068AlphaDummy209] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCphi (Class.cv (nb068AlphaDummy204))))))).fv ∪
        ((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCphi (Class.cv (nb068AlphaDummy204))))))).fv)
      0

theorem nb068_fresh_022 (f : Var) :
    (nb068AlphaDummy234 f) ∉
      (((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy234] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_023 (f : Var) :
    (nb068AlphaDummy210 f) ∉
      (((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCphi (Class.cv (nb068AlphaDummy206 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCphi (Class.cv (nb068AlphaDummy206 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy210] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCphi (Class.cv (nb068AlphaDummy206 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCphi (Class.cv (nb068AlphaDummy206 f))))))).fv)
      0

theorem nb068_fresh_024 :
    (nb068AlphaDummy273) ∉
      (((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy273] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_025 :
    (nb068AlphaDummy249) ∉
      (((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCphi (Class.cv (nb068AlphaDummy244))))))).fv ∪
        ((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCphi (Class.cv (nb068AlphaDummy244))))))).fv) :=
  by
  simpa only [nb068AlphaDummy249] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCphi (Class.cv (nb068AlphaDummy244))))))).fv ∪
        ((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCphi (Class.cv (nb068AlphaDummy244))))))).fv)
      0

theorem nb068_fresh_026 (f : Var) :
    (nb068AlphaDummy274 f) ∉
      (((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy274] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_027 (f : Var) :
    (nb068AlphaDummy250 f) ∉
      (((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCphi (Class.cv (nb068AlphaDummy246 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCphi (Class.cv (nb068AlphaDummy246 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy250] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCphi (Class.cv (nb068AlphaDummy246 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCphi (Class.cv (nb068AlphaDummy246 f))))))).fv)
      0

theorem nb068_fresh_028 :
    (nb068AlphaDummy317) ∉
      (((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy317] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_029 :
    (nb068AlphaDummy293) ∉
      (((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCphi (Class.cv (nb068AlphaDummy288))))))).fv ∪
        ((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCphi (Class.cv (nb068AlphaDummy288))))))).fv) :=
  by
  simpa only [nb068AlphaDummy293] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCphi (Class.cv (nb068AlphaDummy288))))))).fv ∪
        ((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCphi (Class.cv (nb068AlphaDummy288))))))).fv)
      0

theorem nb068_fresh_030 (f : Var) :
    (nb068AlphaDummy318 f) ∉
      (((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy318] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_031 (f : Var) :
    (nb068AlphaDummy294 f) ∉
      (((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCphi (Class.cv (nb068AlphaDummy290 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCphi (Class.cv (nb068AlphaDummy290 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy294] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCphi (Class.cv (nb068AlphaDummy290 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCphi (Class.cv (nb068AlphaDummy290 f))))))).fv)
      0

theorem nb068_fresh_032 :
    (nb068AlphaDummy341) ∉
      (((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCphi (Class.cv (nb068AlphaDummy336))))))).fv ∪
        ((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCphi (Class.cv (nb068AlphaDummy336))))))).fv) :=
  by
  simpa only [nb068AlphaDummy341] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCphi (Class.cv (nb068AlphaDummy336))))))).fv ∪
        ((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCphi (Class.cv (nb068AlphaDummy336))))))).fv)
      0

theorem nb068_fresh_033 :
    (nb068AlphaDummy365) ∉
      (((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy365] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_034 (f : Var) :
    (nb068AlphaDummy342 f) ∉
      (((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCphi (Class.cv (nb068AlphaDummy338 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCphi (Class.cv (nb068AlphaDummy338 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy342] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCphi (Class.cv (nb068AlphaDummy338 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCphi (Class.cv (nb068AlphaDummy338 f))))))).fv)
      0

theorem nb068_fresh_035 (f : Var) :
    (nb068AlphaDummy366 f) ∉
      (((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy366] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_036 :
    (nb068AlphaDummy377) ∉
      (((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCphi (Class.cv (nb068AlphaDummy372))))))).fv ∪
        ((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCphi (Class.cv (nb068AlphaDummy372))))))).fv) :=
  by
  simpa only [nb068AlphaDummy377] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCphi (Class.cv (nb068AlphaDummy372))))))).fv ∪
        ((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCphi (Class.cv (nb068AlphaDummy372))))))).fv)
      0

theorem nb068_fresh_037 :
    (nb068AlphaDummy401) ∉
      (((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy401] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy371)
            (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy371))
                (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_038 (f : Var) :
    (nb068AlphaDummy378 f) ∉
      (((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCphi (Class.cv (nb068AlphaDummy374 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCphi (Class.cv (nb068AlphaDummy374 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy378] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCphi (Class.cv (nb068AlphaDummy374 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCphi (Class.cv (nb068AlphaDummy374 f))))))).fv)
      0

theorem nb068_fresh_039 (f : Var) :
    (nb068AlphaDummy402 f) ∉
      (((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy402] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy373 f)
            (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_040 :
    (nb068AlphaDummy419) ∉
      (((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCphi (Class.cv (nb068AlphaDummy414))))))).fv ∪
        ((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCphi (Class.cv (nb068AlphaDummy414))))))).fv) :=
  by
  simpa only [nb068AlphaDummy419] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCphi (Class.cv (nb068AlphaDummy414))))))).fv ∪
        ((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCphi (Class.cv (nb068AlphaDummy414))))))).fv)
      0

theorem nb068_fresh_041 :
    (nb068AlphaDummy443) ∉
      (((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy443] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy413)
            (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy413))
                (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                  (synCsn (synC0c))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part005`. -/


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

theorem nb068_fresh_042 (f : Var) :
    (nb068AlphaDummy420 f) ∉
      (((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCphi (Class.cv (nb068AlphaDummy416 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCphi (Class.cv (nb068AlphaDummy416 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy420] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCphi (Class.cv (nb068AlphaDummy416 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCphi (Class.cv (nb068AlphaDummy416 f))))))).fv)
      0

theorem nb068_fresh_043 (f : Var) :
    (nb068AlphaDummy444 f) ∉
      (((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy444] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy415 f)
            (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_044 :
    (nb068AlphaDummy479) ∉
      (((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy479] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_045 :
    (nb068AlphaDummy455) ∉
      (((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCphi (Class.cv (nb068AlphaDummy450))))))).fv ∪
        ((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCphi (Class.cv (nb068AlphaDummy450))))))).fv) :=
  by
  simpa only [nb068AlphaDummy455] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCphi (Class.cv (nb068AlphaDummy450))))))).fv ∪
        ((Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCphi (Class.cv (nb068AlphaDummy450))))))).fv)
      0

theorem nb068_fresh_046 (f : Var) :
    (nb068AlphaDummy480 f) ∉
      (((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy480] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_047 (f : Var) :
    (nb068AlphaDummy456 f) ∉
      (((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCphi (Class.cv (nb068AlphaDummy452 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCphi (Class.cv (nb068AlphaDummy452 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy456] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCphi (Class.cv (nb068AlphaDummy452 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCphi (Class.cv (nb068AlphaDummy452 f))))))).fv)
      0

theorem nb068_fresh_048 :
    (nb068AlphaDummy515) ∉
      (((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy515] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_049 :
    (nb068AlphaDummy491) ∉
      (((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCphi (Class.cv (nb068AlphaDummy486))))))).fv ∪
        ((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCphi (Class.cv (nb068AlphaDummy486))))))).fv) :=
  by
  simpa only [nb068AlphaDummy491] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCphi (Class.cv (nb068AlphaDummy486))))))).fv ∪
        ((Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCphi (Class.cv (nb068AlphaDummy486))))))).fv)
      0

theorem nb068_fresh_050 (f : Var) :
    (nb068AlphaDummy516 f) ∉
      (((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb068AlphaDummy516] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb068_fresh_051 (f : Var) :
    (nb068AlphaDummy492 f) ∉
      (((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCphi (Class.cv (nb068AlphaDummy488 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCphi (Class.cv (nb068AlphaDummy488 f))))))).fv) :=
  by
  simpa only [nb068AlphaDummy492] using
    freshVar_not_mem
      (((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCphi (Class.cv (nb068AlphaDummy488 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCphi (Class.cv (nb068AlphaDummy488 f))))))).fv)
      0

theorem nb068_fresh_052 :
    (nb068AlphaDummy125) ∉ (((Class.cv (nb068AlphaDummy000))).fv) := by
  simpa only [nb068AlphaDummy125] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy000))).fv) 0

theorem nb068_fresh_053 :
    (nb068AlphaDummy126) ∉ (((Class.cv (nb068AlphaDummy000))).fv) := by
  simpa only [nb068AlphaDummy126] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy000))).fv) 1

theorem nb068_distinct_054 : (nb068AlphaDummy125) ≠ (nb068AlphaDummy126) := by
  simpa only [nb068AlphaDummy125, nb068AlphaDummy126] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_055 :
    (nb068AlphaDummy045) ∉
      (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) :=
  by
  simpa only [nb068AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
      0

theorem nb068_fresh_056 :
    (nb068AlphaDummy046) ∉
      (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) :=
  by
  simpa only [nb068AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
      1

theorem nb068_fresh_057 :
    (nb068AlphaDummy047) ∉
      (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) :=
  by
  simpa only [nb068AlphaDummy047] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
      2

theorem nb068_distinct_058 : (nb068AlphaDummy045) ≠ (nb068AlphaDummy046) := by
  simpa only [nb068AlphaDummy045, nb068AlphaDummy046] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_059 : (nb068AlphaDummy045) ≠ (nb068AlphaDummy047) := by
  simpa only [nb068AlphaDummy045, nb068AlphaDummy047] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_060 : (nb068AlphaDummy046) ≠ (nb068AlphaDummy047) := by
  simpa only [nb068AlphaDummy046, nb068AlphaDummy047] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_061 :
    (nb068AlphaDummy283) ∉
      (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb068AlphaDummy283] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv) 0

theorem nb068_fresh_062 :
    (nb068AlphaDummy284) ∉
      (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb068AlphaDummy284] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv) 1

theorem nb068_distinct_063 : (nb068AlphaDummy283) ≠ (nb068AlphaDummy284) := by
  simpa only [nb068AlphaDummy283, nb068AlphaDummy284] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_fresh_064 :
    (nb068AlphaDummy005) ∉
      (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv) :=
  by
  simpa only [nb068AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv)
      0

theorem nb068_fresh_065 :
    (nb068AlphaDummy006) ∉
      (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv) :=
  by
  simpa only [nb068AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv)
      1

theorem nb068_distinct_066 : (nb068AlphaDummy005) ≠ (nb068AlphaDummy006) := by
  simpa only [nb068AlphaDummy005, nb068AlphaDummy006] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_067 :
    (nb068AlphaDummy013) ∉ (((Class.cv (nb068AlphaDummy006))).fv) := by
  simpa only [nb068AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy006))).fv) 0

theorem nb068_fresh_068 :
    (nb068AlphaDummy014) ∉ (((Class.cv (nb068AlphaDummy006))).fv) := by
  simpa only [nb068AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy006))).fv) 1

theorem nb068_distinct_069 : (nb068AlphaDummy013) ≠ (nb068AlphaDummy014) := by
  simpa only [nb068AlphaDummy013, nb068AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy006))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_070 (x : Var) (y : Var) :
    (nb068AlphaDummy015 x y) ∉ (((Class.cv (nb068AlphaDummy008 x y))).fv) := by
  simpa only [nb068AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy008 x y))).fv) 0

theorem nb068_fresh_071 (x : Var) (y : Var) :
    (nb068AlphaDummy016 x y) ∉ (((Class.cv (nb068AlphaDummy008 x y))).fv) := by
  simpa only [nb068AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy008 x y))).fv) 1

theorem nb068_distinct_072 (x : Var) (y : Var) :
    (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy016 x y) := by
  simpa only [nb068AlphaDummy015, nb068AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy008 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_073 :
    (nb068AlphaDummy019) ∉
      (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_074 :
    (nb068AlphaDummy020) ∉
      (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_075 :
    (nb068AlphaDummy021) ∉
      (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_076 : (nb068AlphaDummy019) ≠ (nb068AlphaDummy020) := by
  simpa only [nb068AlphaDummy019, nb068AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_077 : (nb068AlphaDummy019) ≠ (nb068AlphaDummy021) := by
  simpa only [nb068AlphaDummy019, nb068AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_078 : (nb068AlphaDummy020) ≠ (nb068AlphaDummy021) := by
  simpa only [nb068AlphaDummy020, nb068AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_079 (x : Var) (y : Var) :
    (nb068AlphaDummy022 x y) ∉
      (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_080 (x : Var) (y : Var) :
    (nb068AlphaDummy023 x y) ∉
      (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_081 (x : Var) (y : Var) :
    (nb068AlphaDummy024 x y) ∉
      (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_082 (x : Var) (y : Var) :
    (nb068AlphaDummy022 x y) ≠ (nb068AlphaDummy023 x y) := by
  simpa only [nb068AlphaDummy022, nb068AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_distinct_083 (x : Var) (y : Var) :
    (nb068AlphaDummy022 x y) ≠ (nb068AlphaDummy024 x y) := by
  simpa only [nb068AlphaDummy022, nb068AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb068_distinct_084 (x : Var) (y : Var) :
    (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy024 x y) := by
  simpa only [nb068AlphaDummy023, nb068AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb068_fresh_085 :
    (nb068AlphaDummy031) ∉
      (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy020))).fv) :=
  by
  simpa only [nb068AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy020))).fv)
      0

theorem nb068_fresh_086 :
    (nb068AlphaDummy027) ∉
      (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv) :=
  by
  simpa only [nb068AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv)
      0

theorem nb068_fresh_087 :
    (nb068AlphaDummy033) ∉
      (((Class.cv (nb068AlphaDummy021))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv) :=
  by
  simpa only [nb068AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy021))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv)
      0

theorem nb068_fresh_088 (x : Var) (y : Var) :
    (nb068AlphaDummy032 x y) ∉
      (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy023 x y))).fv) :=
  by
  simpa only [nb068AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy023 x y))).fv)
      0

theorem nb068_fresh_089 (x : Var) (y : Var) :
    (nb068AlphaDummy028 x y) ∉
      (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy024 x y))).fv) :=
  by
  simpa only [nb068AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy024 x y))).fv)
      0

theorem nb068_fresh_090 (x : Var) (y : Var) :
    (nb068AlphaDummy034 x y) ∉
      (((Class.cv (nb068AlphaDummy024 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy024 x y))).fv) :=
  by
  simpa only [nb068AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy024 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy024 x y))).fv)
      0

theorem nb068_fresh_091 :
    (nb068AlphaDummy053) ∉
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) :=
  by
  simpa only [nb068AlphaDummy053] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv)
      0

theorem nb068_fresh_092 :
    (nb068AlphaDummy054) ∉
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) :=
  by
  simpa only [nb068AlphaDummy054] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv)
      1

theorem nb068_distinct_093 : (nb068AlphaDummy053) ≠ (nb068AlphaDummy054) := by
  simpa only [nb068AlphaDummy053, nb068AlphaDummy054] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_094 :
    (nb068AlphaDummy089) ∉
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv) :=
  by
  simpa only [nb068AlphaDummy089] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv)
      0

theorem nb068_fresh_095 :
    (nb068AlphaDummy090) ∉
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv) :=
  by
  simpa only [nb068AlphaDummy090] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv)
      1

theorem nb068_distinct_096 : (nb068AlphaDummy089) ≠ (nb068AlphaDummy090) := by
  simpa only [nb068AlphaDummy089, nb068AlphaDummy090] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_097 :
    (nb068AlphaDummy203) ∉
      (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) :=
  by
  simpa only [nb068AlphaDummy203] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv)
      0

theorem nb068_fresh_098 :
    (nb068AlphaDummy204) ∉
      (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) :=
  by
  simpa only [nb068AlphaDummy204] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv)
      1

theorem nb068_distinct_099 : (nb068AlphaDummy203) ≠ (nb068AlphaDummy204) := by
  simpa only [nb068AlphaDummy203, nb068AlphaDummy204] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_100 (f : Var) :
    (nb068AlphaDummy055 f) ∉
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) :=
  by
  simpa only [nb068AlphaDummy055] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv)
      0

theorem nb068_fresh_101 (f : Var) :
    (nb068AlphaDummy056 f) ∉
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) :=
  by
  simpa only [nb068AlphaDummy056] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv)
      1

theorem nb068_distinct_102 (f : Var) :
    (nb068AlphaDummy055 f) ≠ (nb068AlphaDummy056 f) := by
  simpa only [nb068AlphaDummy055, nb068AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy048 f))).fv ∪
        ((Class.cv (nb068AlphaDummy049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_103 (f : Var) :
    (nb068AlphaDummy091 f) ∉
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy050 f))).fv) :=
  by
  simpa only [nb068AlphaDummy091] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy050 f))).fv)
      0

theorem nb068_fresh_104 (f : Var) :
    (nb068AlphaDummy092 f) ∉
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy050 f))).fv) :=
  by
  simpa only [nb068AlphaDummy092] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy050 f))).fv)
      1

theorem nb068_distinct_105 (f : Var) :
    (nb068AlphaDummy091 f) ≠ (nb068AlphaDummy092 f) := by
  simpa only [nb068AlphaDummy091, nb068AlphaDummy092] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy048 f))).fv ∪
        ((Class.cv (nb068AlphaDummy050 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_106 (f : Var) :
    (nb068AlphaDummy205 f) ∉
      (((Class.cv (nb068AlphaDummy050 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) :=
  by
  simpa only [nb068AlphaDummy205] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy050 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv)
      0

theorem nb068_fresh_107 (f : Var) :
    (nb068AlphaDummy206 f) ∉
      (((Class.cv (nb068AlphaDummy050 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) :=
  by
  simpa only [nb068AlphaDummy206] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy050 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv)
      1

theorem nb068_distinct_108 (f : Var) :
    (nb068AlphaDummy205 f) ≠ (nb068AlphaDummy206 f) := by
  simpa only [nb068AlphaDummy205, nb068AlphaDummy206] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy050 f))).fv ∪
        ((Class.cv (nb068AlphaDummy049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_109 :
    (nb068AlphaDummy061) ∉ (((Class.cv (nb068AlphaDummy054))).fv) := by
  simpa only [nb068AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy054))).fv) 0

theorem nb068_fresh_110 :
    (nb068AlphaDummy062) ∉ (((Class.cv (nb068AlphaDummy054))).fv) := by
  simpa only [nb068AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy054))).fv) 1

theorem nb068_distinct_111 : (nb068AlphaDummy061) ≠ (nb068AlphaDummy062) := by
  simpa only [nb068AlphaDummy061, nb068AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy054))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_112 (f : Var) :
    (nb068AlphaDummy063 f) ∉ (((Class.cv (nb068AlphaDummy056 f))).fv) := by
  simpa only [nb068AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy056 f))).fv) 0

theorem nb068_fresh_113 (f : Var) :
    (nb068AlphaDummy064 f) ∉ (((Class.cv (nb068AlphaDummy056 f))).fv) := by
  simpa only [nb068AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy056 f))).fv) 1

theorem nb068_distinct_114 (f : Var) :
    (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy064 f) := by
  simpa only [nb068AlphaDummy063, nb068AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy056 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_115 :
    (nb068AlphaDummy067) ∉
      (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy067] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_116 :
    (nb068AlphaDummy068) ∉
      (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy068] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_117 :
    (nb068AlphaDummy069) ∉
      (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy069] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_118 : (nb068AlphaDummy067) ≠ (nb068AlphaDummy068) := by
  simpa only [nb068AlphaDummy067, nb068AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_119 : (nb068AlphaDummy067) ≠ (nb068AlphaDummy069) := by
  simpa only [nb068AlphaDummy067, nb068AlphaDummy069] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_120 : (nb068AlphaDummy068) ≠ (nb068AlphaDummy069) := by
  simpa only [nb068AlphaDummy068, nb068AlphaDummy069] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_121 (f : Var) :
    (nb068AlphaDummy070 f) ∉
      (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy070] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_122 (f : Var) :
    (nb068AlphaDummy071 f) ∉
      (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy071] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_123 (f : Var) :
    (nb068AlphaDummy072 f) ∉
      (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy072] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_124 (f : Var) :
    (nb068AlphaDummy070 f) ≠ (nb068AlphaDummy071 f) := by
  simpa only [nb068AlphaDummy070, nb068AlphaDummy071] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_125 (f : Var) :
    (nb068AlphaDummy070 f) ≠ (nb068AlphaDummy072 f) := by
  simpa only [nb068AlphaDummy070, nb068AlphaDummy072] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_126 (f : Var) :
    (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy072 f) := by
  simpa only [nb068AlphaDummy071, nb068AlphaDummy072] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_127 :
    (nb068AlphaDummy079) ∉
      (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy068))).fv) :=
  by
  simpa only [nb068AlphaDummy079] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy068))).fv)
      0

theorem nb068_fresh_128 :
    (nb068AlphaDummy075) ∉
      (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv) :=
  by
  simpa only [nb068AlphaDummy075] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv)
      0

theorem nb068_fresh_129 :
    (nb068AlphaDummy081) ∉
      (((Class.cv (nb068AlphaDummy069))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv) :=
  by
  simpa only [nb068AlphaDummy081] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy069))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv)
      0

theorem nb068_fresh_130 (f : Var) :
    (nb068AlphaDummy080 f) ∉
      (((Class.cv (nb068AlphaDummy071 f))).fv ∪ ((Class.cv (nb068AlphaDummy071 f))).fv) :=
  by
  simpa only [nb068AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy071 f))).fv ∪ ((Class.cv (nb068AlphaDummy071 f))).fv)
      0

theorem nb068_fresh_131 (f : Var) :
    (nb068AlphaDummy076 f) ∉
      (((Class.cv (nb068AlphaDummy071 f))).fv ∪ ((Class.cv (nb068AlphaDummy072 f))).fv) :=
  by
  simpa only [nb068AlphaDummy076] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy071 f))).fv ∪ ((Class.cv (nb068AlphaDummy072 f))).fv)
      0

theorem nb068_fresh_132 (f : Var) :
    (nb068AlphaDummy082 f) ∉
      (((Class.cv (nb068AlphaDummy072 f))).fv ∪ ((Class.cv (nb068AlphaDummy072 f))).fv) :=
  by
  simpa only [nb068AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy072 f))).fv ∪ ((Class.cv (nb068AlphaDummy072 f))).fv)
      0

theorem nb068_fresh_133 :
    (nb068AlphaDummy097) ∉ (((Class.cv (nb068AlphaDummy090))).fv) := by
  simpa only [nb068AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy090))).fv) 0

theorem nb068_fresh_134 :
    (nb068AlphaDummy098) ∉ (((Class.cv (nb068AlphaDummy090))).fv) := by
  simpa only [nb068AlphaDummy098] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy090))).fv) 1

theorem nb068_distinct_135 : (nb068AlphaDummy097) ≠ (nb068AlphaDummy098) := by
  simpa only [nb068AlphaDummy097, nb068AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy090))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_136 (f : Var) :
    (nb068AlphaDummy099 f) ∉ (((Class.cv (nb068AlphaDummy092 f))).fv) := by
  simpa only [nb068AlphaDummy099] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy092 f))).fv) 0

theorem nb068_fresh_137 (f : Var) :
    (nb068AlphaDummy100 f) ∉ (((Class.cv (nb068AlphaDummy092 f))).fv) := by
  simpa only [nb068AlphaDummy100] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy092 f))).fv) 1

theorem nb068_distinct_138 (f : Var) :
    (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy100 f) := by
  simpa only [nb068AlphaDummy099, nb068AlphaDummy100] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy092 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_139 :
    (nb068AlphaDummy103) ∉
      (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy103] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_140 :
    (nb068AlphaDummy104) ∉
      (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy104] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_141 :
    (nb068AlphaDummy105) ∉
      (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy105] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_142 : (nb068AlphaDummy103) ≠ (nb068AlphaDummy104) := by
  simpa only [nb068AlphaDummy103, nb068AlphaDummy104] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_143 : (nb068AlphaDummy103) ≠ (nb068AlphaDummy105) := by
  simpa only [nb068AlphaDummy103, nb068AlphaDummy105] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_144 : (nb068AlphaDummy104) ≠ (nb068AlphaDummy105) := by
  simpa only [nb068AlphaDummy104, nb068AlphaDummy105] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_145 (f : Var) :
    (nb068AlphaDummy106 f) ∉
      (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy106] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_146 (f : Var) :
    (nb068AlphaDummy107 f) ∉
      (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy107] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_147 (f : Var) :
    (nb068AlphaDummy108 f) ∉
      (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy108] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_148 (f : Var) :
    (nb068AlphaDummy106 f) ≠ (nb068AlphaDummy107 f) := by
  simpa only [nb068AlphaDummy106, nb068AlphaDummy107] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_149 (f : Var) :
    (nb068AlphaDummy106 f) ≠ (nb068AlphaDummy108 f) := by
  simpa only [nb068AlphaDummy106, nb068AlphaDummy108] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_150 (f : Var) :
    (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy108 f) := by
  simpa only [nb068AlphaDummy107, nb068AlphaDummy108] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_151 :
    (nb068AlphaDummy115) ∉
      (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy104))).fv) :=
  by
  simpa only [nb068AlphaDummy115] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy104))).fv)
      0

theorem nb068_fresh_152 :
    (nb068AlphaDummy111) ∉
      (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv) :=
  by
  simpa only [nb068AlphaDummy111] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv)
      0

theorem nb068_fresh_153 :
    (nb068AlphaDummy117) ∉
      (((Class.cv (nb068AlphaDummy105))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv) :=
  by
  simpa only [nb068AlphaDummy117] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy105))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv)
      0

theorem nb068_fresh_154 (f : Var) :
    (nb068AlphaDummy116 f) ∉
      (((Class.cv (nb068AlphaDummy107 f))).fv ∪ ((Class.cv (nb068AlphaDummy107 f))).fv) :=
  by
  simpa only [nb068AlphaDummy116] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy107 f))).fv ∪ ((Class.cv (nb068AlphaDummy107 f))).fv)
      0

theorem nb068_fresh_155 (f : Var) :
    (nb068AlphaDummy112 f) ∉
      (((Class.cv (nb068AlphaDummy107 f))).fv ∪ ((Class.cv (nb068AlphaDummy108 f))).fv) :=
  by
  simpa only [nb068AlphaDummy112] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy107 f))).fv ∪ ((Class.cv (nb068AlphaDummy108 f))).fv)
      0

theorem nb068_fresh_156 (f : Var) :
    (nb068AlphaDummy118 f) ∉
      (((Class.cv (nb068AlphaDummy108 f))).fv ∪ ((Class.cv (nb068AlphaDummy108 f))).fv) :=
  by
  simpa only [nb068AlphaDummy118] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy108 f))).fv ∪ ((Class.cv (nb068AlphaDummy108 f))).fv)
      0

theorem nb068_fresh_157 :
    (nb068AlphaDummy131) ∉
      (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv) :=
  by
  simpa only [nb068AlphaDummy131] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv)
      0

theorem nb068_fresh_158 :
    (nb068AlphaDummy132) ∉
      (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv) :=
  by
  simpa only [nb068AlphaDummy132] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv)
      1

theorem nb068_distinct_159 : (nb068AlphaDummy131) ≠ (nb068AlphaDummy132) := by
  simpa only [nb068AlphaDummy131, nb068AlphaDummy132] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_160 :
    (nb068AlphaDummy167) ∉
      (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv) :=
  by
  simpa only [nb068AlphaDummy167] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv)
      0

theorem nb068_fresh_161 :
    (nb068AlphaDummy168) ∉
      (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv) :=
  by
  simpa only [nb068AlphaDummy168] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv)
      1

theorem nb068_distinct_162 : (nb068AlphaDummy167) ≠ (nb068AlphaDummy168) := by
  simpa only [nb068AlphaDummy167, nb068AlphaDummy168] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_163 (f : Var) :
    (nb068AlphaDummy133 f) ∉
      (((Class.cv (nb068AlphaDummy127 f))).fv ∪ ((Class.cv (nb068AlphaDummy128 f))).fv) :=
  by
  simpa only [nb068AlphaDummy133] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy127 f))).fv ∪ ((Class.cv (nb068AlphaDummy128 f))).fv)
      0

theorem nb068_fresh_164 (f : Var) :
    (nb068AlphaDummy134 f) ∉
      (((Class.cv (nb068AlphaDummy127 f))).fv ∪ ((Class.cv (nb068AlphaDummy128 f))).fv) :=
  by
  simpa only [nb068AlphaDummy134] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy127 f))).fv ∪ ((Class.cv (nb068AlphaDummy128 f))).fv)
      1

theorem nb068_distinct_165 (f : Var) :
    (nb068AlphaDummy133 f) ≠ (nb068AlphaDummy134 f) := by
  simpa only [nb068AlphaDummy133, nb068AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy127 f))).fv ∪
        ((Class.cv (nb068AlphaDummy128 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_166 (f : Var) :
    (nb068AlphaDummy169 f) ∉
      (((Class.cv (nb068AlphaDummy128 f))).fv ∪ ((Class.cv (nb068AlphaDummy127 f))).fv) :=
  by
  simpa only [nb068AlphaDummy169] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy128 f))).fv ∪ ((Class.cv (nb068AlphaDummy127 f))).fv)
      0

theorem nb068_fresh_167 (f : Var) :
    (nb068AlphaDummy170 f) ∉
      (((Class.cv (nb068AlphaDummy128 f))).fv ∪ ((Class.cv (nb068AlphaDummy127 f))).fv) :=
  by
  simpa only [nb068AlphaDummy170] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy128 f))).fv ∪ ((Class.cv (nb068AlphaDummy127 f))).fv)
      1

theorem nb068_distinct_168 (f : Var) :
    (nb068AlphaDummy169 f) ≠ (nb068AlphaDummy170 f) := by
  simpa only [nb068AlphaDummy169, nb068AlphaDummy170] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
        ((Class.cv (nb068AlphaDummy127 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_169 :
    (nb068AlphaDummy139) ∉ (((Class.cv (nb068AlphaDummy132))).fv) := by
  simpa only [nb068AlphaDummy139] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy132))).fv) 0

theorem nb068_fresh_170 :
    (nb068AlphaDummy140) ∉ (((Class.cv (nb068AlphaDummy132))).fv) := by
  simpa only [nb068AlphaDummy140] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy132))).fv) 1

theorem nb068_distinct_171 : (nb068AlphaDummy139) ≠ (nb068AlphaDummy140) := by
  simpa only [nb068AlphaDummy139, nb068AlphaDummy140] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_172 (f : Var) :
    (nb068AlphaDummy141 f) ∉ (((Class.cv (nb068AlphaDummy134 f))).fv) := by
  simpa only [nb068AlphaDummy141] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy134 f))).fv) 0

theorem nb068_fresh_173 (f : Var) :
    (nb068AlphaDummy142 f) ∉ (((Class.cv (nb068AlphaDummy134 f))).fv) := by
  simpa only [nb068AlphaDummy142] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy134 f))).fv) 1

theorem nb068_distinct_174 (f : Var) :
    (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy142 f) := by
  simpa only [nb068AlphaDummy141, nb068AlphaDummy142] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_175 :
    (nb068AlphaDummy145) ∉
      (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy145] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_176 :
    (nb068AlphaDummy146) ∉
      (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy146] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_177 :
    (nb068AlphaDummy147) ∉
      (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy147] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_178 : (nb068AlphaDummy145) ≠ (nb068AlphaDummy146) := by
  simpa only [nb068AlphaDummy145, nb068AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_179 : (nb068AlphaDummy145) ≠ (nb068AlphaDummy147) := by
  simpa only [nb068AlphaDummy145, nb068AlphaDummy147] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_180 : (nb068AlphaDummy146) ≠ (nb068AlphaDummy147) := by
  simpa only [nb068AlphaDummy146, nb068AlphaDummy147] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_181 (f : Var) :
    (nb068AlphaDummy148 f) ∉
      (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy148] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_182 (f : Var) :
    (nb068AlphaDummy149 f) ∉
      (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy149] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_183 (f : Var) :
    (nb068AlphaDummy150 f) ∉
      (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy150] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_184 (f : Var) :
    (nb068AlphaDummy148 f) ≠ (nb068AlphaDummy149 f) := by
  simpa only [nb068AlphaDummy148, nb068AlphaDummy149] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_185 (f : Var) :
    (nb068AlphaDummy148 f) ≠ (nb068AlphaDummy150 f) := by
  simpa only [nb068AlphaDummy148, nb068AlphaDummy150] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_186 (f : Var) :
    (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy150 f) := by
  simpa only [nb068AlphaDummy149, nb068AlphaDummy150] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_187 :
    (nb068AlphaDummy157) ∉
      (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy146))).fv) :=
  by
  simpa only [nb068AlphaDummy157] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy146))).fv)
      0

theorem nb068_fresh_188 :
    (nb068AlphaDummy153) ∉
      (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv) :=
  by
  simpa only [nb068AlphaDummy153] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv)
      0

theorem nb068_fresh_189 :
    (nb068AlphaDummy159) ∉
      (((Class.cv (nb068AlphaDummy147))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv) :=
  by
  simpa only [nb068AlphaDummy159] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy147))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv)
      0

theorem nb068_fresh_190 (f : Var) :
    (nb068AlphaDummy158 f) ∉
      (((Class.cv (nb068AlphaDummy149 f))).fv ∪ ((Class.cv (nb068AlphaDummy149 f))).fv) :=
  by
  simpa only [nb068AlphaDummy158] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy149 f))).fv ∪ ((Class.cv (nb068AlphaDummy149 f))).fv)
      0

theorem nb068_fresh_191 (f : Var) :
    (nb068AlphaDummy154 f) ∉
      (((Class.cv (nb068AlphaDummy149 f))).fv ∪ ((Class.cv (nb068AlphaDummy150 f))).fv) :=
  by
  simpa only [nb068AlphaDummy154] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy149 f))).fv ∪ ((Class.cv (nb068AlphaDummy150 f))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
