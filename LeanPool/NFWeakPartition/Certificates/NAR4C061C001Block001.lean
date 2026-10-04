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

/-! Certificates from `NAR4C061C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_000`. -/
@[expose]
noncomputable def nb061AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_001`. -/
@[expose]
noncomputable def nb061AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_002`. -/
@[expose]
noncomputable def nb061AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_003`. -/
@[expose]
noncomputable def nb061AlphaDummy003 : Var :=
  (freshVar
    (({(nb061AlphaDummy001)} : Finset Var) ∪ ({(nb061AlphaDummy000)} : Finset Var) ∪
      ((synWral (nb061AlphaDummy002) (Class.cv (nb061AlphaDummy000))
          (synWbr (Class.cv (nb061AlphaDummy002)) (Class.cv (nb061AlphaDummy001))
            (Class.cv (nb061AlphaDummy002))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_004`. -/
@[expose]
noncomputable def nb061AlphaDummy004 (x : Var) (r : Var) (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ((synWral x (Class.cv a) (synWbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_005`. -/
@[expose]
noncomputable def nb061AlphaDummy005 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_006`. -/
@[expose]
noncomputable def nb061AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_007`. -/
@[expose]
noncomputable def nb061AlphaDummy007 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_008`. -/
@[expose]
noncomputable def nb061AlphaDummy008 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_009`. -/
@[expose]
noncomputable def nb061AlphaDummy009 : Var :=
  (freshVar (((synCcompl (Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCphi (Class.cv (nb061AlphaDummy006)))))))).fv ∪ ((synCcompl
          (Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_010`. -/
@[expose]
noncomputable def nb061AlphaDummy010 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCphi (Class.cv (nb061AlphaDummy008 r a)))))))).fv ∪ ((synCcompl
          (Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_011`. -/
@[expose]
noncomputable def nb061AlphaDummy011 : Var :=
  (freshVar (((Class.cab (nb061AlphaDummy005)
          (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
            (Wff.classEq (Class.cv (nb061AlphaDummy005))
              (synCphi (Class.cv (nb061AlphaDummy006))))))).fv ∪
      ((Class.cab (nb061AlphaDummy005)
          (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
            (Wff.classEq (Class.cv (nb061AlphaDummy005))
              (synCphi (Class.cv (nb061AlphaDummy006))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_012`. -/
@[expose]
noncomputable def nb061AlphaDummy012 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb061AlphaDummy007 r a)
          (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
              (synCphi (Class.cv (nb061AlphaDummy008 r a))))))).fv ∪
      ((Class.cab (nb061AlphaDummy007 r a) (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
              (synCphi (Class.cv (nb061AlphaDummy008 r a))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_013`. -/
@[expose]
noncomputable def nb061AlphaDummy013 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy006))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_014`. -/
@[expose]
noncomputable def nb061AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy006))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_015`. -/
@[expose]
noncomputable def nb061AlphaDummy015 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy008 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_016`. -/
@[expose]
noncomputable def nb061AlphaDummy016 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy008 r a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_017`. -/
@[expose]
noncomputable def nb061AlphaDummy017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb061AlphaDummy013)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb061AlphaDummy013)) (synC1c))).fv ∪
      ((Class.cv (nb061AlphaDummy013))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_018`. -/
@[expose]
noncomputable def nb061AlphaDummy018 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb061AlphaDummy015 r a)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb061AlphaDummy015 r a)) (synC1c))).fv ∪
      ((Class.cv (nb061AlphaDummy015 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_019`. -/
@[expose]
noncomputable def nb061AlphaDummy019 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_020`. -/
@[expose]
noncomputable def nb061AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_021`. -/
@[expose]
noncomputable def nb061AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_022`. -/
@[expose]
noncomputable def nb061AlphaDummy022 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_023`. -/
@[expose]
noncomputable def nb061AlphaDummy023 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_024`. -/
@[expose]
noncomputable def nb061AlphaDummy024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_025`. -/
@[expose]
noncomputable def nb061AlphaDummy025 : Var :=
  (freshVar (((synCnin (Class.cv (nb061AlphaDummy020))
          (Class.cv (nb061AlphaDummy021)))).fv ∪
      ((synCnin (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_026`. -/
@[expose]
noncomputable def nb061AlphaDummy026 (r : Var) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb061AlphaDummy023 r a))
          (Class.cv (nb061AlphaDummy024 r a)))).fv ∪
      ((synCnin (Class.cv (nb061AlphaDummy023 r a))
          (Class.cv (nb061AlphaDummy024 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_027`. -/
@[expose]
noncomputable def nb061AlphaDummy027 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_028`. -/
@[expose]
noncomputable def nb061AlphaDummy028 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
      ((Class.cv (nb061AlphaDummy024 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_029`. -/
@[expose]
noncomputable def nb061AlphaDummy029 : Var :=
  (freshVar (((synCcompl (Class.cv (nb061AlphaDummy020)))).fv ∪
      ((synCcompl (Class.cv (nb061AlphaDummy021)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_030`. -/
@[expose]
noncomputable def nb061AlphaDummy030 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb061AlphaDummy023 r a)))).fv ∪
      ((synCcompl (Class.cv (nb061AlphaDummy024 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_031`. -/
@[expose]
noncomputable def nb061AlphaDummy031 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_032`. -/
@[expose]
noncomputable def nb061AlphaDummy032 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
      ((Class.cv (nb061AlphaDummy023 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_033`. -/
@[expose]
noncomputable def nb061AlphaDummy033 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy021))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_034`. -/
@[expose]
noncomputable def nb061AlphaDummy034 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy024 r a))).fv ∪
      ((Class.cv (nb061AlphaDummy024 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_035`. -/
@[expose]
noncomputable def nb061AlphaDummy035 : Var :=
  (freshVar (((Class.cab (nb061AlphaDummy005)
          (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
            (Wff.classEq (Class.cv (nb061AlphaDummy005))
              (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy005)
          (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
            (Wff.classEq (Class.cv (nb061AlphaDummy005))
              (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_036`. -/
@[expose]
noncomputable def nb061AlphaDummy036 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb061AlphaDummy007 r a)
          (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
              (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy007 r a)
          (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
              (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_037`. -/
@[expose]
noncomputable def nb061AlphaDummy037 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb061AlphaDummy006))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_038`. -/
@[expose]
noncomputable def nb061AlphaDummy038 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb061AlphaDummy008 r a))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_039`. -/
@[expose]
noncomputable def nb061AlphaDummy039 : Var :=
  (freshVar (((synCphi (Class.cv (nb061AlphaDummy006)))).fv ∪
      ((synCphi (Class.cv (nb061AlphaDummy006)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_040`. -/
@[expose]
noncomputable def nb061AlphaDummy040 (r : Var) (a : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb061AlphaDummy008 r a)))).fv ∪
      ((synCphi (Class.cv (nb061AlphaDummy008 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_041`. -/
@[expose]
noncomputable def nb061AlphaDummy041 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy002))).fv ∪ ((Class.cv (nb061AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_042`. -/
@[expose]
noncomputable def nb061AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy002))).fv ∪ ((Class.cv (nb061AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_043`. -/
@[expose]
noncomputable def nb061AlphaDummy043 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_044`. -/
@[expose]
noncomputable def nb061AlphaDummy044 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_045`. -/
@[expose]
noncomputable def nb061AlphaDummy045 : Var :=
  (freshVar (((synCcompl (Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCphi (Class.cv (nb061AlphaDummy042)))))))).fv ∪ ((synCcompl
          (Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_046`. -/
@[expose]
noncomputable def nb061AlphaDummy046 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb061AlphaDummy043 x)
            (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCphi (Class.cv (nb061AlphaDummy044 x)))))))).fv ∪ ((synCcompl
          (Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_047`. -/
@[expose]
noncomputable def nb061AlphaDummy047 : Var :=
  (freshVar (((Class.cab (nb061AlphaDummy041)
          (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
            (Wff.classEq (Class.cv (nb061AlphaDummy041))
              (synCphi (Class.cv (nb061AlphaDummy042))))))).fv ∪
      ((Class.cab (nb061AlphaDummy041)
          (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
            (Wff.classEq (Class.cv (nb061AlphaDummy041))
              (synCphi (Class.cv (nb061AlphaDummy042))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_048`. -/
@[expose]
noncomputable def nb061AlphaDummy048 (x : Var) : Var :=
  (freshVar (((Class.cab (nb061AlphaDummy043 x)
          (synWrex (nb061AlphaDummy044 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
              (synCphi (Class.cv (nb061AlphaDummy044 x))))))).fv ∪
      ((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
              (synCphi (Class.cv (nb061AlphaDummy044 x))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_049`. -/
@[expose]
noncomputable def nb061AlphaDummy049 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy042))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_050`. -/
@[expose]
noncomputable def nb061AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy042))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_051`. -/
@[expose]
noncomputable def nb061AlphaDummy051 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy044 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_052`. -/
@[expose]
noncomputable def nb061AlphaDummy052 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy044 x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_053`. -/
@[expose]
noncomputable def nb061AlphaDummy053 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb061AlphaDummy049)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb061AlphaDummy049)) (synC1c))).fv ∪
      ((Class.cv (nb061AlphaDummy049))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_054`. -/
@[expose]
noncomputable def nb061AlphaDummy054 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb061AlphaDummy051 x)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb061AlphaDummy051 x)) (synC1c))).fv ∪
      ((Class.cv (nb061AlphaDummy051 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_055`. -/
@[expose]
noncomputable def nb061AlphaDummy055 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_056`. -/
@[expose]
noncomputable def nb061AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_057`. -/
@[expose]
noncomputable def nb061AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_058`. -/
@[expose]
noncomputable def nb061AlphaDummy058 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_059`. -/
@[expose]
noncomputable def nb061AlphaDummy059 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_060`. -/
@[expose]
noncomputable def nb061AlphaDummy060 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_061`. -/
@[expose]
noncomputable def nb061AlphaDummy061 : Var :=
  (freshVar (((synCnin (Class.cv (nb061AlphaDummy056))
          (Class.cv (nb061AlphaDummy057)))).fv ∪
      ((synCnin (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_062`. -/
@[expose]
noncomputable def nb061AlphaDummy062 (x : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb061AlphaDummy059 x))
          (Class.cv (nb061AlphaDummy060 x)))).fv ∪
      ((synCnin (Class.cv (nb061AlphaDummy059 x)) (Class.cv (nb061AlphaDummy060 x)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_063`. -/
@[expose]
noncomputable def nb061AlphaDummy063 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_064`. -/
@[expose]
noncomputable def nb061AlphaDummy064 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy059 x))).fv ∪
      ((Class.cv (nb061AlphaDummy060 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_065`. -/
@[expose]
noncomputable def nb061AlphaDummy065 : Var :=
  (freshVar (((synCcompl (Class.cv (nb061AlphaDummy056)))).fv ∪
      ((synCcompl (Class.cv (nb061AlphaDummy057)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_066`. -/
@[expose]
noncomputable def nb061AlphaDummy066 (x : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb061AlphaDummy059 x)))).fv ∪
      ((synCcompl (Class.cv (nb061AlphaDummy060 x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_067`. -/
@[expose]
noncomputable def nb061AlphaDummy067 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy056))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_068`. -/
@[expose]
noncomputable def nb061AlphaDummy068 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy059 x))).fv ∪
      ((Class.cv (nb061AlphaDummy059 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_069`. -/
@[expose]
noncomputable def nb061AlphaDummy069 : Var :=
  (freshVar
    (((Class.cv (nb061AlphaDummy057))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_070`. -/
@[expose]
noncomputable def nb061AlphaDummy070 (x : Var) : Var :=
  (freshVar (((Class.cv (nb061AlphaDummy060 x))).fv ∪
      ((Class.cv (nb061AlphaDummy060 x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_071`. -/
@[expose]
noncomputable def nb061AlphaDummy071 : Var :=
  (freshVar (((Class.cab (nb061AlphaDummy041)
          (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
            (Wff.classEq (Class.cv (nb061AlphaDummy041))
              (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy041)
          (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
            (Wff.classEq (Class.cv (nb061AlphaDummy041))
              (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_072`. -/
@[expose]
noncomputable def nb061AlphaDummy072 (x : Var) : Var :=
  (freshVar (((Class.cab (nb061AlphaDummy043 x)
          (synWrex (nb061AlphaDummy044 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
              (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy043 x)
          (synWrex (nb061AlphaDummy044 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
              (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_073`. -/
@[expose]
noncomputable def nb061AlphaDummy073 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb061AlphaDummy042))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_074`. -/
@[expose]
noncomputable def nb061AlphaDummy074 (x : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb061AlphaDummy044 x))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_075`. -/
@[expose]
noncomputable def nb061AlphaDummy075 : Var :=
  (freshVar (((synCphi (Class.cv (nb061AlphaDummy042)))).fv ∪
      ((synCphi (Class.cv (nb061AlphaDummy042)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb061_alpha_dummy_076`. -/
@[expose]
noncomputable def nb061AlphaDummy076 (x : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb061AlphaDummy044 x)))).fv ∪
      ((synCphi (Class.cv (nb061AlphaDummy044 x)))).fv) 0)

theorem nb061_fresh_000 :
    (nb061AlphaDummy035) ∉
      (((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb061AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb061_fresh_001 :
    (nb061AlphaDummy011) ∉
      (((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCphi (Class.cv (nb061AlphaDummy006))))))).fv ∪
        ((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCphi (Class.cv (nb061AlphaDummy006))))))).fv) :=
  by
  simpa only [nb061AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCphi (Class.cv (nb061AlphaDummy006))))))).fv ∪
        ((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCphi (Class.cv (nb061AlphaDummy006))))))).fv)
      0

theorem nb061_fresh_002 (r : Var) (a : Var) :
    (nb061AlphaDummy036 r a) ∉
      (((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb061AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb061_fresh_003 (r : Var) (a : Var) :
    (nb061AlphaDummy012 r a) ∉
      (((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCphi (Class.cv (nb061AlphaDummy008 r a))))))).fv ∪
        ((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCphi (Class.cv (nb061AlphaDummy008 r a))))))).fv) :=
  by
  simpa only [nb061AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCphi (Class.cv (nb061AlphaDummy008 r a))))))).fv ∪
        ((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCphi (Class.cv (nb061AlphaDummy008 r a))))))).fv)
      0

theorem nb061_fresh_004 :
    (nb061AlphaDummy047) ∉
      (((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCphi (Class.cv (nb061AlphaDummy042))))))).fv ∪
        ((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCphi (Class.cv (nb061AlphaDummy042))))))).fv) :=
  by
  simpa only [nb061AlphaDummy047] using
    freshVar_not_mem
      (((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCphi (Class.cv (nb061AlphaDummy042))))))).fv ∪
        ((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCphi (Class.cv (nb061AlphaDummy042))))))).fv)
      0

theorem nb061_fresh_005 :
    (nb061AlphaDummy071) ∉
      (((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb061AlphaDummy071] using
    freshVar_not_mem
      (((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb061_fresh_006 (x : Var) :
    (nb061AlphaDummy048 x) ∉
      (((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCphi (Class.cv (nb061AlphaDummy044 x))))))).fv ∪
        ((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCphi (Class.cv (nb061AlphaDummy044 x))))))).fv) :=
  by
  simpa only [nb061AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCphi (Class.cv (nb061AlphaDummy044 x))))))).fv ∪
        ((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCphi (Class.cv (nb061AlphaDummy044 x))))))).fv)
      0

theorem nb061_fresh_007 (x : Var) :
    (nb061AlphaDummy072 x) ∉
      (((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy043 x)
            (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb061AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy043 x)
            (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb061_fresh_008 :
    (nb061AlphaDummy005) ∉
      (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv) :=
  by
  simpa only [nb061AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv)
      0

theorem nb061_fresh_009 :
    (nb061AlphaDummy006) ∉
      (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv) :=
  by
  simpa only [nb061AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv)
      1

theorem nb061_distinct_010 : (nb061AlphaDummy005) ≠ (nb061AlphaDummy006) := by
  simpa only [nb061AlphaDummy005, nb061AlphaDummy006] using
    (freshVar_injective
      (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb061_fresh_011 :
    (nb061AlphaDummy041) ∉
      (((Class.cv (nb061AlphaDummy002))).fv ∪ ((Class.cv (nb061AlphaDummy002))).fv) :=
  by
  simpa only [nb061AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy002))).fv ∪ ((Class.cv (nb061AlphaDummy002))).fv)
      0

theorem nb061_fresh_012 :
    (nb061AlphaDummy042) ∉
      (((Class.cv (nb061AlphaDummy002))).fv ∪ ((Class.cv (nb061AlphaDummy002))).fv) :=
  by
  simpa only [nb061AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy002))).fv ∪ ((Class.cv (nb061AlphaDummy002))).fv)
      1

theorem nb061_distinct_013 : (nb061AlphaDummy041) ≠ (nb061AlphaDummy042) := by
  simpa only [nb061AlphaDummy041, nb061AlphaDummy042] using
    (freshVar_injective
      (((Class.cv (nb061AlphaDummy002))).fv ∪ ((Class.cv (nb061AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb061_fresh_014 :
    (nb061AlphaDummy013) ∉ (((Class.cv (nb061AlphaDummy006))).fv) := by
  simpa only [nb061AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy006))).fv) 0

theorem nb061_fresh_015 :
    (nb061AlphaDummy014) ∉ (((Class.cv (nb061AlphaDummy006))).fv) := by
  simpa only [nb061AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy006))).fv) 1

theorem nb061_distinct_016 : (nb061AlphaDummy013) ≠ (nb061AlphaDummy014) := by
  simpa only [nb061AlphaDummy013, nb061AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy006))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_017 (r : Var) (a : Var) :
    (nb061AlphaDummy015 r a) ∉ (((Class.cv (nb061AlphaDummy008 r a))).fv) := by
  simpa only [nb061AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy008 r a))).fv) 0

theorem nb061_fresh_018 (r : Var) (a : Var) :
    (nb061AlphaDummy016 r a) ∉ (((Class.cv (nb061AlphaDummy008 r a))).fv) := by
  simpa only [nb061AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy008 r a))).fv) 1

theorem nb061_distinct_019 (r : Var) (a : Var) :
    (nb061AlphaDummy015 r a) ≠ (nb061AlphaDummy016 r a) := by
  simpa only [nb061AlphaDummy015, nb061AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy008 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb061_fresh_020 :
    (nb061AlphaDummy019) ∉
      (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) 0

theorem nb061_fresh_021 :
    (nb061AlphaDummy020) ∉
      (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) 1

theorem nb061_fresh_022 :
    (nb061AlphaDummy021) ∉
      (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) 2

theorem nb061_distinct_023 : (nb061AlphaDummy019) ≠ (nb061AlphaDummy020) := by
  simpa only [nb061AlphaDummy019, nb061AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb061_distinct_024 : (nb061AlphaDummy019) ≠ (nb061AlphaDummy021) := by
  simpa only [nb061AlphaDummy019, nb061AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb061_distinct_025 : (nb061AlphaDummy020) ≠ (nb061AlphaDummy021) := by
  simpa only [nb061AlphaDummy020, nb061AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb061_fresh_026 (r : Var) (a : Var) :
    (nb061AlphaDummy022 r a) ∉
      (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) 0

theorem nb061_fresh_027 (r : Var) (a : Var) :
    (nb061AlphaDummy023 r a) ∉
      (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) 1

theorem nb061_fresh_028 (r : Var) (a : Var) :
    (nb061AlphaDummy024 r a) ∉
      (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) 2

theorem nb061_distinct_029 (r : Var) (a : Var) :
    (nb061AlphaDummy022 r a) ≠ (nb061AlphaDummy023 r a) := by
  simpa only [nb061AlphaDummy022, nb061AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb061_distinct_030 (r : Var) (a : Var) :
    (nb061AlphaDummy022 r a) ≠ (nb061AlphaDummy024 r a) := by
  simpa only [nb061AlphaDummy022, nb061AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb061_distinct_031 (r : Var) (a : Var) :
    (nb061AlphaDummy023 r a) ≠ (nb061AlphaDummy024 r a) := by
  simpa only [nb061AlphaDummy023, nb061AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb061_fresh_032 :
    (nb061AlphaDummy031) ∉
      (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy020))).fv) :=
  by
  simpa only [nb061AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy020))).fv)
      0

theorem nb061_fresh_033 :
    (nb061AlphaDummy027) ∉
      (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv) :=
  by
  simpa only [nb061AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv)
      0

theorem nb061_fresh_034 :
    (nb061AlphaDummy033) ∉
      (((Class.cv (nb061AlphaDummy021))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv) :=
  by
  simpa only [nb061AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy021))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv)
      0

theorem nb061_fresh_035 (r : Var) (a : Var) :
    (nb061AlphaDummy032 r a) ∉
      (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy023 r a))).fv) :=
  by
  simpa only [nb061AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy023 r a))).fv)
      0

theorem nb061_fresh_036 (r : Var) (a : Var) :
    (nb061AlphaDummy028 r a) ∉
      (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy024 r a))).fv) :=
  by
  simpa only [nb061AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy024 r a))).fv)
      0

theorem nb061_fresh_037 (r : Var) (a : Var) :
    (nb061AlphaDummy034 r a) ∉
      (((Class.cv (nb061AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy024 r a))).fv) :=
  by
  simpa only [nb061AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy024 r a))).fv)
      0

theorem nb061_fresh_038 :
    (nb061AlphaDummy049) ∉ (((Class.cv (nb061AlphaDummy042))).fv) := by
  simpa only [nb061AlphaDummy049] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy042))).fv) 0

theorem nb061_fresh_039 :
    (nb061AlphaDummy050) ∉ (((Class.cv (nb061AlphaDummy042))).fv) := by
  simpa only [nb061AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy042))).fv) 1

theorem nb061_distinct_040 : (nb061AlphaDummy049) ≠ (nb061AlphaDummy050) := by
  simpa only [nb061AlphaDummy049, nb061AlphaDummy050] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy042))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_041 (x : Var) :
    (nb061AlphaDummy051 x) ∉ (((Class.cv (nb061AlphaDummy044 x))).fv) := by
  simpa only [nb061AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy044 x))).fv) 0

theorem nb061_fresh_042 (x : Var) :
    (nb061AlphaDummy052 x) ∉ (((Class.cv (nb061AlphaDummy044 x))).fv) := by
  simpa only [nb061AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy044 x))).fv) 1

theorem nb061_distinct_043 (x : Var) :
    (nb061AlphaDummy051 x) ≠ (nb061AlphaDummy052 x) := by
  simpa only [nb061AlphaDummy051, nb061AlphaDummy052] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy044 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb061_fresh_044 :
    (nb061AlphaDummy055) ∉
      (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy055] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) 0

theorem nb061_fresh_045 :
    (nb061AlphaDummy056) ∉
      (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) 1

theorem nb061_fresh_046 :
    (nb061AlphaDummy057) ∉
      (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) 2

theorem nb061_distinct_047 : (nb061AlphaDummy055) ≠ (nb061AlphaDummy056) := by
  simpa only [nb061AlphaDummy055, nb061AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb061_distinct_048 : (nb061AlphaDummy055) ≠ (nb061AlphaDummy057) := by
  simpa only [nb061AlphaDummy055, nb061AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb061_distinct_049 : (nb061AlphaDummy056) ≠ (nb061AlphaDummy057) := by
  simpa only [nb061AlphaDummy056, nb061AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb061_fresh_050 (x : Var) :
    (nb061AlphaDummy058 x) ∉
      (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) 0

theorem nb061_fresh_051 (x : Var) :
    (nb061AlphaDummy059 x) ∉
      (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) 1

theorem nb061_fresh_052 (x : Var) :
    (nb061AlphaDummy060 x) ∉
      (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb061AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) 2

theorem nb061_distinct_053 (x : Var) :
    (nb061AlphaDummy058 x) ≠ (nb061AlphaDummy059 x) := by
  simpa only [nb061AlphaDummy058, nb061AlphaDummy059] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb061_distinct_054 (x : Var) :
    (nb061AlphaDummy058 x) ≠ (nb061AlphaDummy060 x) := by
  simpa only [nb061AlphaDummy058, nb061AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb061_distinct_055 (x : Var) :
    (nb061AlphaDummy059 x) ≠ (nb061AlphaDummy060 x) := by
  simpa only [nb061AlphaDummy059, nb061AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb061_fresh_056 :
    (nb061AlphaDummy067) ∉
      (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy056))).fv) :=
  by
  simpa only [nb061AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy056))).fv)
      0

theorem nb061_fresh_057 :
    (nb061AlphaDummy063) ∉
      (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv) :=
  by
  simpa only [nb061AlphaDummy063] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv)
      0

theorem nb061_fresh_058 :
    (nb061AlphaDummy069) ∉
      (((Class.cv (nb061AlphaDummy057))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv) :=
  by
  simpa only [nb061AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy057))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv)
      0

theorem nb061_fresh_059 (x : Var) :
    (nb061AlphaDummy068 x) ∉
      (((Class.cv (nb061AlphaDummy059 x))).fv ∪ ((Class.cv (nb061AlphaDummy059 x))).fv) :=
  by
  simpa only [nb061AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy059 x))).fv ∪ ((Class.cv (nb061AlphaDummy059 x))).fv)
      0

theorem nb061_fresh_060 (x : Var) :
    (nb061AlphaDummy064 x) ∉
      (((Class.cv (nb061AlphaDummy059 x))).fv ∪ ((Class.cv (nb061AlphaDummy060 x))).fv) :=
  by
  simpa only [nb061AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy059 x))).fv ∪ ((Class.cv (nb061AlphaDummy060 x))).fv)
      0

theorem nb061_fresh_061 (x : Var) :
    (nb061AlphaDummy070 x) ∉
      (((Class.cv (nb061AlphaDummy060 x))).fv ∪ ((Class.cv (nb061AlphaDummy060 x))).fv) :=
  by
  simpa only [nb061AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb061AlphaDummy060 x))).fv ∪ ((Class.cv (nb061AlphaDummy060 x))).fv)
      0

theorem nb061_fresh_062 (r : Var) (a : Var) :
    (nb061AlphaDummy007 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb061AlphaDummy007] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb061_fresh_063 (r : Var) (a : Var) :
    (nb061AlphaDummy008 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb061AlphaDummy008] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb061_distinct_064 (r : Var) (a : Var) :
    (nb061AlphaDummy007 r a) ≠ (nb061AlphaDummy008 r a) := by
  simpa only [nb061AlphaDummy007, nb061AlphaDummy008] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_065 (x : Var) :
    (nb061AlphaDummy043 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb061AlphaDummy043] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0

theorem nb061_fresh_066 (x : Var) :
    (nb061AlphaDummy044 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb061AlphaDummy044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 1

theorem nb061_distinct_067 (x : Var) :
    (nb061AlphaDummy043 x) ≠ (nb061AlphaDummy044 x) := by
  simpa only [nb061AlphaDummy043, nb061AlphaDummy044] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_068 :
    (nb061AlphaDummy017) ∉
      (((Wff.classMem (Class.cv (nb061AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy013))).fv) :=
  by
  simpa only [nb061AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb061AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy013))).fv)
      0

theorem nb061_fresh_069 (r : Var) (a : Var) :
    (nb061AlphaDummy018 r a) ∉
      (((Wff.classMem (Class.cv (nb061AlphaDummy015 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy015 r a)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy015 r a))).fv) :=
  by
  simpa only [nb061AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb061AlphaDummy015 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy015 r a)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy015 r a))).fv)
      0

theorem nb061_fresh_070 :
    (nb061AlphaDummy053) ∉
      (((Wff.classMem (Class.cv (nb061AlphaDummy049)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy049)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy049))).fv) :=
  by
  simpa only [nb061AlphaDummy053] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb061AlphaDummy049)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy049)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy049))).fv)
      0

theorem nb061_fresh_071 (x : Var) :
    (nb061AlphaDummy054 x) ∉
      (((Wff.classMem (Class.cv (nb061AlphaDummy051 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy051 x)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy051 x))).fv) :=
  by
  simpa only [nb061AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb061AlphaDummy051 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy051 x)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy051 x))).fv)
      0

theorem nb061_fresh_072 :
    (nb061AlphaDummy009) ∉
      (((synCcompl (Class.cab (nb061AlphaDummy005)
              (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
                (Wff.classEq (Class.cv (nb061AlphaDummy005))
                  (synCphi (Class.cv (nb061AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy005)
              (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
                (Wff.classEq (Class.cv (nb061AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb061AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb061AlphaDummy005)
              (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
                (Wff.classEq (Class.cv (nb061AlphaDummy005))
                  (synCphi (Class.cv (nb061AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy005)
              (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
                (Wff.classEq (Class.cv (nb061AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C061C001Part002`. -/


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

theorem nb061_fresh_073 (r : Var) (a : Var) :
    (nb061AlphaDummy010 r a) ∉
      (((synCcompl (Class.cab (nb061AlphaDummy007 r a)
              (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                  (synCphi (Class.cv (nb061AlphaDummy008 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy007 r a)
              (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb061AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb061AlphaDummy007 r a)
              (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                  (synCphi (Class.cv (nb061AlphaDummy008 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy007 r a)
              (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb061_fresh_074 :
    (nb061AlphaDummy045) ∉
      (((synCcompl (Class.cab (nb061AlphaDummy041)
              (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
                (Wff.classEq (Class.cv (nb061AlphaDummy041))
                  (synCphi (Class.cv (nb061AlphaDummy042)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy041)
              (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
                (Wff.classEq (Class.cv (nb061AlphaDummy041))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb061AlphaDummy045] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb061AlphaDummy041)
              (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
                (Wff.classEq (Class.cv (nb061AlphaDummy041))
                  (synCphi (Class.cv (nb061AlphaDummy042)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy041)
              (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
                (Wff.classEq (Class.cv (nb061AlphaDummy041))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb061_fresh_075 (x : Var) :
    (nb061AlphaDummy046 x) ∉
      (((synCcompl (Class.cab (nb061AlphaDummy043 x)
              (synWrex (nb061AlphaDummy044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                  (synCphi (Class.cv (nb061AlphaDummy044 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy043 x)
              (synWrex (nb061AlphaDummy044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb061AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb061AlphaDummy043 x)
              (synWrex (nb061AlphaDummy044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                  (synCphi (Class.cv (nb061AlphaDummy044 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy043 x)
              (synWrex (nb061AlphaDummy044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb061_fresh_076 :
    (nb061AlphaDummy029) ∉
      (((synCcompl (Class.cv (nb061AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy021)))).fv) :=
  by
  simpa only [nb061AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb061AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy021)))).fv)
      0

theorem nb061_fresh_077 (r : Var) (a : Var) :
    (nb061AlphaDummy030 r a) ∉
      (((synCcompl (Class.cv (nb061AlphaDummy023 r a)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy024 r a)))).fv) :=
  by
  simpa only [nb061AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb061AlphaDummy023 r a)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy024 r a)))).fv)
      0

theorem nb061_fresh_078 :
    (nb061AlphaDummy065) ∉
      (((synCcompl (Class.cv (nb061AlphaDummy056)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy057)))).fv) :=
  by
  simpa only [nb061AlphaDummy065] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb061AlphaDummy056)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy057)))).fv)
      0

theorem nb061_fresh_079 (x : Var) :
    (nb061AlphaDummy066 x) ∉
      (((synCcompl (Class.cv (nb061AlphaDummy059 x)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy060 x)))).fv) :=
  by
  simpa only [nb061AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb061AlphaDummy059 x)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy060 x)))).fv)
      0

theorem nb061_fresh_080 :
    (nb061AlphaDummy037) ∉
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb061AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb061_fresh_081 (r : Var) (a : Var) :
    (nb061AlphaDummy038 r a) ∉
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy008 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb061AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy008 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb061_fresh_082 :
    (nb061AlphaDummy073) ∉
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy042))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb061AlphaDummy073] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy042))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb061_fresh_083 (x : Var) :
    (nb061AlphaDummy074 x) ∉
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy044 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb061AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy044 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb061_fresh_084 :
    (nb061AlphaDummy025) ∉
      (((synCnin (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy020))
            (Class.cv (nb061AlphaDummy021)))).fv) :=
  by
  simpa only [nb061AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021)))).fv)
      0

theorem nb061_fresh_085 (r : Var) (a : Var) :
    (nb061AlphaDummy026 r a) ∉
      (((synCnin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a)))).fv) :=
  by
  simpa only [nb061AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a)))).fv)
      0

theorem nb061_fresh_086 :
    (nb061AlphaDummy061) ∉
      (((synCnin (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy056))
            (Class.cv (nb061AlphaDummy057)))).fv) :=
  by
  simpa only [nb061AlphaDummy061] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057)))).fv)
      0

theorem nb061_fresh_087 (x : Var) :
    (nb061AlphaDummy062 x) ∉
      (((synCnin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x)))).fv) :=
  by
  simpa only [nb061AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x)))).fv)
      0

theorem nb061_fresh_088 :
    (nb061AlphaDummy039) ∉
      (((synCphi (Class.cv (nb061AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy006)))).fv) :=
  by
  simpa only [nb061AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb061AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy006)))).fv)
      0

theorem nb061_fresh_089 (r : Var) (a : Var) :
    (nb061AlphaDummy040 r a) ∉
      (((synCphi (Class.cv (nb061AlphaDummy008 r a)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy008 r a)))).fv) :=
  by
  simpa only [nb061AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb061AlphaDummy008 r a)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy008 r a)))).fv)
      0

theorem nb061_fresh_090 :
    (nb061AlphaDummy075) ∉
      (((synCphi (Class.cv (nb061AlphaDummy042)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy042)))).fv) :=
  by
  simpa only [nb061AlphaDummy075] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb061AlphaDummy042)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy042)))).fv)
      0

theorem nb061_fresh_091 (x : Var) :
    (nb061AlphaDummy076 x) ∉
      (((synCphi (Class.cv (nb061AlphaDummy044 x)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy044 x)))).fv) :=
  by
  simpa only [nb061AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb061AlphaDummy044 x)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy044 x)))).fv)
      0

theorem nb061_fresh_092 :
    (nb061AlphaDummy003) ∉
      (({(nb061AlphaDummy001)} : Finset Var) ∪ ({(nb061AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb061AlphaDummy002) (Class.cv (nb061AlphaDummy000))
            (synWbr (Class.cv (nb061AlphaDummy002)) (Class.cv (nb061AlphaDummy001))
              (Class.cv (nb061AlphaDummy002))))).fv) :=
  by
  simpa only [nb061AlphaDummy003] using
    freshVar_not_mem
      (({(nb061AlphaDummy001)} : Finset Var) ∪ ({(nb061AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb061AlphaDummy002) (Class.cv (nb061AlphaDummy000))
            (synWbr (Class.cv (nb061AlphaDummy002)) (Class.cv (nb061AlphaDummy001))
              (Class.cv (nb061AlphaDummy002))))).fv)
      0

theorem nb061_fresh_093 (x : Var) (r : Var) (a : Var) :
    (nb061AlphaDummy004 x r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) :=
  by
  simpa only [nb061AlphaDummy004] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪
        ((synWral x (Class.cv a) (synWbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv)
      0

theorem nb061_fresh_094 : (nb061AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb061AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb061_fresh_095 : (nb061AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb061AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb061_fresh_096 : (nb061AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb061AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb061_distinct_097 : (nb061AlphaDummy000) ≠ (nb061AlphaDummy001) := by
  simpa only [nb061AlphaDummy000, nb061AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb061_distinct_098 : (nb061AlphaDummy000) ≠ (nb061AlphaDummy002) := by
  simpa only [nb061AlphaDummy000, nb061AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb061_distinct_099 : (nb061AlphaDummy001) ≠ (nb061AlphaDummy002) := by
  simpa only [nb061AlphaDummy001, nb061AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb061_support_mem_0000 :
    (nb061AlphaDummy001) ∈
      (({(nb061AlphaDummy001)} : Finset Var) ∪ ({(nb061AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb061AlphaDummy002) (Class.cv (nb061AlphaDummy000))
            (synWbr (Class.cv (nb061AlphaDummy002)) (Class.cv (nb061AlphaDummy001))
              (Class.cv (nb061AlphaDummy002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0001 (x : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0002 :
    (nb061AlphaDummy000) ∈
      (({(nb061AlphaDummy001)} : Finset Var) ∪ ({(nb061AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb061AlphaDummy002) (Class.cv (nb061AlphaDummy000))
            (synWbr (Class.cv (nb061AlphaDummy002)) (Class.cv (nb061AlphaDummy001))
              (Class.cv (nb061AlphaDummy002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0003 (x : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0004 :
    (nb061AlphaDummy001) ∈
      (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0005 :
    (nb061AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb061AlphaDummy005)
              (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
                (Wff.classEq (Class.cv (nb061AlphaDummy005))
                  (synCphi (Class.cv (nb061AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy005)
              (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
                (Wff.classEq (Class.cv (nb061AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((synCcompl (Class.cab (nb061AlphaDummy007 r a)
              (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                  (synCphi (Class.cv (nb061AlphaDummy008 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy007 r a)
              (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0008 :
    (nb061AlphaDummy001) ∈
      (((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCphi (Class.cv (nb061AlphaDummy006))))))).fv ∪
        ((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCphi (Class.cv (nb061AlphaDummy006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCphi (Class.cv (nb061AlphaDummy008 r a))))))).fv ∪
        ((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCphi (Class.cv (nb061AlphaDummy008 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0010 :
    (nb061AlphaDummy006) ∈ (((Class.cv (nb061AlphaDummy006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0011 (r : Var) (a : Var) :
    (nb061AlphaDummy008 r a) ∈ (((Class.cv (nb061AlphaDummy008 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0012 :
    (nb061AlphaDummy013) ∈
      (((Wff.classMem (Class.cv (nb061AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy013))).fv) :=
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

theorem nb061_support_mem_0013 (r : Var) (a : Var) :
    (nb061AlphaDummy015 r a) ∈
      (((Wff.classMem (Class.cv (nb061AlphaDummy015 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy015 r a)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy015 r a))).fv) :=
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

theorem nb061_support_mem_0014 :
    (nb061AlphaDummy013) ∈
      (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0015 (r : Var) (a : Var) :
    (nb061AlphaDummy015 r a) ∈
      (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0016 :
    (nb061AlphaDummy020) ∈
      (((synCnin (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy020))
            (Class.cv (nb061AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0017 (r : Var) (a : Var) :
    (nb061AlphaDummy023 r a) ∈
      (((synCnin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0018 :
    (nb061AlphaDummy020) ∈
      (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0019 (r : Var) (a : Var) :
    (nb061AlphaDummy023 r a) ∈
      (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0020 :
    (nb061AlphaDummy021) ∈
      (((synCnin (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy020))
            (Class.cv (nb061AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0021 (r : Var) (a : Var) :
    (nb061AlphaDummy024 r a) ∈
      (((synCnin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0022 :
    (nb061AlphaDummy021) ∈
      (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0023 (r : Var) (a : Var) :
    (nb061AlphaDummy024 r a) ∈
      (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0024 :
    (nb061AlphaDummy020) ∈
      (((synCcompl (Class.cv (nb061AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0025 (r : Var) (a : Var) :
    (nb061AlphaDummy023 r a) ∈
      (((synCcompl (Class.cv (nb061AlphaDummy023 r a)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy024 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0026 :
    (nb061AlphaDummy020) ∈
      (((Class.cv (nb061AlphaDummy020))).fv ∪ ((Class.cv (nb061AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0027 (r : Var) (a : Var) :
    (nb061AlphaDummy023 r a) ∈
      (((Class.cv (nb061AlphaDummy023 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy023 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0028 :
    (nb061AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb061AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0029 (r : Var) (a : Var) :
    (nb061AlphaDummy024 r a) ∈
      (((synCcompl (Class.cv (nb061AlphaDummy023 r a)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy024 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0030 :
    (nb061AlphaDummy021) ∈
      (((Class.cv (nb061AlphaDummy021))).fv ∪ ((Class.cv (nb061AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0031 (r : Var) (a : Var) :
    (nb061AlphaDummy024 r a) ∈
      (((Class.cv (nb061AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb061AlphaDummy024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0032 :
    (nb061AlphaDummy000) ∈
      (((Class.cv (nb061AlphaDummy001))).fv ∪ ((Class.cv (nb061AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0033 :
    (nb061AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb061AlphaDummy005)
              (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy001))
                (Wff.classEq (Class.cv (nb061AlphaDummy005))
                  (synCphi (Class.cv (nb061AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy005)
              (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
                (Wff.classEq (Class.cv (nb061AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((synCcompl (Class.cab (nb061AlphaDummy007 r a)
              (synWrex (nb061AlphaDummy008 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                  (synCphi (Class.cv (nb061AlphaDummy008 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy007 r a)
              (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0036 :
    (nb061AlphaDummy000) ∈
      (((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy005)
            (synWrex (nb061AlphaDummy006) (Class.cv (nb061AlphaDummy000))
              (Wff.classEq (Class.cv (nb061AlphaDummy005))
                (synCun (synCphi (Class.cv (nb061AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy007 r a)
            (synWrex (nb061AlphaDummy008 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
                (synCun (synCphi (Class.cv (nb061AlphaDummy008 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0038 :
    (nb061AlphaDummy006) ∈
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0039 (r : Var) (a : Var) :
    (nb061AlphaDummy008 r a) ∈
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy008 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0040 :
    (nb061AlphaDummy006) ∈
      (((synCphi (Class.cv (nb061AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0041 (r : Var) (a : Var) :
    (nb061AlphaDummy008 r a) ∈
      (((synCphi (Class.cv (nb061AlphaDummy008 r a)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy008 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0042 :
    (nb061AlphaDummy002) ∈
      (((Class.cv (nb061AlphaDummy002))).fv ∪ ((Class.cv (nb061AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0043 :
    (nb061AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb061AlphaDummy041)
              (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
                (Wff.classEq (Class.cv (nb061AlphaDummy041))
                  (synCphi (Class.cv (nb061AlphaDummy042)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy041)
              (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
                (Wff.classEq (Class.cv (nb061AlphaDummy041))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0044 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0045 (x : Var) :
    x ∈
      (((synCcompl (Class.cab (nb061AlphaDummy043 x)
              (synWrex (nb061AlphaDummy044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                  (synCphi (Class.cv (nb061AlphaDummy044 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb061AlphaDummy043 x)
              (synWrex (nb061AlphaDummy044 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                  (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0046 :
    (nb061AlphaDummy002) ∈
      (((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCphi (Class.cv (nb061AlphaDummy042))))))).fv ∪
        ((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCphi (Class.cv (nb061AlphaDummy042))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0047 (x : Var) :
    x ∈
      (((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCphi (Class.cv (nb061AlphaDummy044 x))))))).fv ∪
        ((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCphi (Class.cv (nb061AlphaDummy044 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0048 :
    (nb061AlphaDummy042) ∈ (((Class.cv (nb061AlphaDummy042))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0049 (x : Var) :
    (nb061AlphaDummy044 x) ∈ (((Class.cv (nb061AlphaDummy044 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0050 :
    (nb061AlphaDummy049) ∈
      (((Wff.classMem (Class.cv (nb061AlphaDummy049)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy049)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy049))).fv) :=
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

theorem nb061_support_mem_0051 (x : Var) :
    (nb061AlphaDummy051 x) ∈
      (((Wff.classMem (Class.cv (nb061AlphaDummy051 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb061AlphaDummy051 x)) (synC1c))).fv ∪
        ((Class.cv (nb061AlphaDummy051 x))).fv) :=
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

theorem nb061_support_mem_0052 :
    (nb061AlphaDummy049) ∈
      (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0053 (x : Var) :
    (nb061AlphaDummy051 x) ∈
      (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0054 :
    (nb061AlphaDummy056) ∈
      (((synCnin (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy056))
            (Class.cv (nb061AlphaDummy057)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0055 (x : Var) :
    (nb061AlphaDummy059 x) ∈
      (((synCnin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0056 :
    (nb061AlphaDummy056) ∈
      (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0057 (x : Var) :
    (nb061AlphaDummy059 x) ∈
      (((Class.cv (nb061AlphaDummy059 x))).fv ∪ ((Class.cv (nb061AlphaDummy060 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0058 :
    (nb061AlphaDummy057) ∈
      (((synCnin (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy056))
            (Class.cv (nb061AlphaDummy057)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0059 (x : Var) :
    (nb061AlphaDummy060 x) ∈
      (((synCnin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x)))).fv ∪
        ((synCnin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0060 :
    (nb061AlphaDummy057) ∈
      (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0061 (x : Var) :
    (nb061AlphaDummy060 x) ∈
      (((Class.cv (nb061AlphaDummy059 x))).fv ∪ ((Class.cv (nb061AlphaDummy060 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0062 :
    (nb061AlphaDummy056) ∈
      (((synCcompl (Class.cv (nb061AlphaDummy056)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy057)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0063 (x : Var) :
    (nb061AlphaDummy059 x) ∈
      (((synCcompl (Class.cv (nb061AlphaDummy059 x)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy060 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0064 :
    (nb061AlphaDummy056) ∈
      (((Class.cv (nb061AlphaDummy056))).fv ∪ ((Class.cv (nb061AlphaDummy056))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0065 (x : Var) :
    (nb061AlphaDummy059 x) ∈
      (((Class.cv (nb061AlphaDummy059 x))).fv ∪ ((Class.cv (nb061AlphaDummy059 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0066 :
    (nb061AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb061AlphaDummy056)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy057)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0067 (x : Var) :
    (nb061AlphaDummy060 x) ∈
      (((synCcompl (Class.cv (nb061AlphaDummy059 x)))).fv ∪
        ((synCcompl (Class.cv (nb061AlphaDummy060 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0068 :
    (nb061AlphaDummy057) ∈
      (((Class.cv (nb061AlphaDummy057))).fv ∪ ((Class.cv (nb061AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0069 (x : Var) :
    (nb061AlphaDummy060 x) ∈
      (((Class.cv (nb061AlphaDummy060 x))).fv ∪ ((Class.cv (nb061AlphaDummy060 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0070 :
    (nb061AlphaDummy002) ∈
      (((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy041)
            (synWrex (nb061AlphaDummy042) (Class.cv (nb061AlphaDummy002))
              (Wff.classEq (Class.cv (nb061AlphaDummy041))
                (synCun (synCphi (Class.cv (nb061AlphaDummy042)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0071 (x : Var) :
    x ∈
      (((Class.cab (nb061AlphaDummy043 x) (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb061AlphaDummy043 x)
            (synWrex (nb061AlphaDummy044 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
                (synCun (synCphi (Class.cv (nb061AlphaDummy044 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb061_support_mem_0072 :
    (nb061AlphaDummy042) ∈
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy042))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0073 (x : Var) :
    (nb061AlphaDummy044 x) ∈
      (((synCcompl (synCphi (Class.cv (nb061AlphaDummy044 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0074 :
    (nb061AlphaDummy042) ∈
      (((synCphi (Class.cv (nb061AlphaDummy042)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy042)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb061_support_mem_0075 (x : Var) :
    (nb061AlphaDummy044 x) ∈
      (((synCphi (Class.cv (nb061AlphaDummy044 x)))).fv ∪
        ((synCphi (Class.cv (nb061AlphaDummy044 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
