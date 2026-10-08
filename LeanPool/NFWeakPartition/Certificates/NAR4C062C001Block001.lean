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

/-! Certificates from `NAR4C062C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_000`. -/
@[expose]
noncomputable def nb062AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_001`. -/
@[expose]
noncomputable def nb062AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_002`. -/
@[expose]
noncomputable def nb062AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_003`. -/
@[expose]
noncomputable def nb062AlphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_004`. -/
@[expose]
noncomputable def nb062AlphaDummy004 : Var :=
  (freshVar
    (({(nb062AlphaDummy001)} : Finset Var) ∪ ({(nb062AlphaDummy000)} : Finset Var) ∪
      ((synWral (nb062AlphaDummy002) (Class.cv (nb062AlphaDummy000))
          (synWral (nb062AlphaDummy003) (Class.cv (nb062AlphaDummy000)) (Wff.imp (synWa
                (synWbr (Class.cv (nb062AlphaDummy002))
                  (Class.cv (nb062AlphaDummy001)) (Class.cv (nb062AlphaDummy003)))
                (synWbr (Class.cv (nb062AlphaDummy003))
                  (Class.cv (nb062AlphaDummy001)) (Class.cv (nb062AlphaDummy002))))
              (Wff.objEq (nb062AlphaDummy002) (nb062AlphaDummy003)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_005`. -/
@[expose]
noncomputable def nb062AlphaDummy005 (x : Var) (y : Var) (r : Var) (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
          (synWral y (Class.cv a) (Wff.imp
              (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_006`. -/
@[expose]
noncomputable def nb062AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_007`. -/
@[expose]
noncomputable def nb062AlphaDummy007 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_008`. -/
@[expose]
noncomputable def nb062AlphaDummy008 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_009`. -/
@[expose]
noncomputable def nb062AlphaDummy009 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_010`. -/
@[expose]
noncomputable def nb062AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCphi (Class.cv (nb062AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_011`. -/
@[expose]
noncomputable def nb062AlphaDummy011 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCphi (Class.cv (nb062AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
          (Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_012`. -/
@[expose]
noncomputable def nb062AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy006)
          (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
            (Wff.classEq (Class.cv (nb062AlphaDummy006))
              (synCphi (Class.cv (nb062AlphaDummy007))))))).fv ∪
      ((Class.cab (nb062AlphaDummy006)
          (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
            (Wff.classEq (Class.cv (nb062AlphaDummy006))
              (synCphi (Class.cv (nb062AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_013`. -/
@[expose]
noncomputable def nb062AlphaDummy013 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy008 r a)
          (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
              (synCphi (Class.cv (nb062AlphaDummy009 r a))))))).fv ∪
      ((Class.cab (nb062AlphaDummy008 r a) (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
              (synCphi (Class.cv (nb062AlphaDummy009 r a))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_014`. -/
@[expose]
noncomputable def nb062AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_015`. -/
@[expose]
noncomputable def nb062AlphaDummy015 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_016`. -/
@[expose]
noncomputable def nb062AlphaDummy016 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy009 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_017`. -/
@[expose]
noncomputable def nb062AlphaDummy017 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy009 r a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_018`. -/
@[expose]
noncomputable def nb062AlphaDummy018 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062AlphaDummy014)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb062AlphaDummy014)) (synC1c))).fv ∪
      ((Class.cv (nb062AlphaDummy014))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_019`. -/
@[expose]
noncomputable def nb062AlphaDummy019 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062AlphaDummy016 r a)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb062AlphaDummy016 r a)) (synC1c))).fv ∪
      ((Class.cv (nb062AlphaDummy016 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_020`. -/
@[expose]
noncomputable def nb062AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_021`. -/
@[expose]
noncomputable def nb062AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_022`. -/
@[expose]
noncomputable def nb062AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_023`. -/
@[expose]
noncomputable def nb062AlphaDummy023 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_024`. -/
@[expose]
noncomputable def nb062AlphaDummy024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_025`. -/
@[expose]
noncomputable def nb062AlphaDummy025 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_026`. -/
@[expose]
noncomputable def nb062AlphaDummy026 : Var :=
  (freshVar (((synCnin (Class.cv (nb062AlphaDummy021))
          (Class.cv (nb062AlphaDummy022)))).fv ∪
      ((synCnin (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_027`. -/
@[expose]
noncomputable def nb062AlphaDummy027 (r : Var) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb062AlphaDummy024 r a))
          (Class.cv (nb062AlphaDummy025 r a)))).fv ∪
      ((synCnin (Class.cv (nb062AlphaDummy024 r a))
          (Class.cv (nb062AlphaDummy025 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_028`. -/
@[expose]
noncomputable def nb062AlphaDummy028 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_029`. -/
@[expose]
noncomputable def nb062AlphaDummy029 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
      ((Class.cv (nb062AlphaDummy025 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_030`. -/
@[expose]
noncomputable def nb062AlphaDummy030 : Var :=
  (freshVar (((synCcompl (Class.cv (nb062AlphaDummy021)))).fv ∪
      ((synCcompl (Class.cv (nb062AlphaDummy022)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_031`. -/
@[expose]
noncomputable def nb062AlphaDummy031 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb062AlphaDummy024 r a)))).fv ∪
      ((synCcompl (Class.cv (nb062AlphaDummy025 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_032`. -/
@[expose]
noncomputable def nb062AlphaDummy032 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_033`. -/
@[expose]
noncomputable def nb062AlphaDummy033 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
      ((Class.cv (nb062AlphaDummy024 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_034`. -/
@[expose]
noncomputable def nb062AlphaDummy034 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy022))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_035`. -/
@[expose]
noncomputable def nb062AlphaDummy035 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy025 r a))).fv ∪
      ((Class.cv (nb062AlphaDummy025 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_036`. -/
@[expose]
noncomputable def nb062AlphaDummy036 : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy006)
          (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
            (Wff.classEq (Class.cv (nb062AlphaDummy006))
              (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy006)
          (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
            (Wff.classEq (Class.cv (nb062AlphaDummy006))
              (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_037`. -/
@[expose]
noncomputable def nb062AlphaDummy037 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy008 r a)
          (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
              (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy008 r a)
          (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
              (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_038`. -/
@[expose]
noncomputable def nb062AlphaDummy038 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb062AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_039`. -/
@[expose]
noncomputable def nb062AlphaDummy039 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb062AlphaDummy009 r a))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_040`. -/
@[expose]
noncomputable def nb062AlphaDummy040 : Var :=
  (freshVar (((synCphi (Class.cv (nb062AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb062AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_041`. -/
@[expose]
noncomputable def nb062AlphaDummy041 (r : Var) (a : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb062AlphaDummy009 r a)))).fv ∪
      ((synCphi (Class.cv (nb062AlphaDummy009 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_042`. -/
@[expose]
noncomputable def nb062AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_043`. -/
@[expose]
noncomputable def nb062AlphaDummy043 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_044`. -/
@[expose]
noncomputable def nb062AlphaDummy044 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_045`. -/
@[expose]
noncomputable def nb062AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_046`. -/
@[expose]
noncomputable def nb062AlphaDummy046 : Var :=
  (freshVar (((synCcompl (Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCphi (Class.cv (nb062AlphaDummy043)))))))).fv ∪ ((synCcompl
          (Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_047`. -/
@[expose]
noncomputable def nb062AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCphi (Class.cv (nb062AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_048`. -/
@[expose]
noncomputable def nb062AlphaDummy048 : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy042)
          (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
            (Wff.classEq (Class.cv (nb062AlphaDummy042))
              (synCphi (Class.cv (nb062AlphaDummy043))))))).fv ∪
      ((Class.cab (nb062AlphaDummy042)
          (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
            (Wff.classEq (Class.cv (nb062AlphaDummy042))
              (synCphi (Class.cv (nb062AlphaDummy043))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_049`. -/
@[expose]
noncomputable def nb062AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy044 x y)
          (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
              (synCphi (Class.cv (nb062AlphaDummy045 x y))))))).fv ∪
      ((Class.cab (nb062AlphaDummy044 x y) (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
              (synCphi (Class.cv (nb062AlphaDummy045 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_050`. -/
@[expose]
noncomputable def nb062AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy043))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_051`. -/
@[expose]
noncomputable def nb062AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy043))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_052`. -/
@[expose]
noncomputable def nb062AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy045 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_053`. -/
@[expose]
noncomputable def nb062AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy045 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_054`. -/
@[expose]
noncomputable def nb062AlphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062AlphaDummy050)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb062AlphaDummy050)) (synC1c))).fv ∪
      ((Class.cv (nb062AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_055`. -/
@[expose]
noncomputable def nb062AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb062AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb062AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_056`. -/
@[expose]
noncomputable def nb062AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_057`. -/
@[expose]
noncomputable def nb062AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_058`. -/
@[expose]
noncomputable def nb062AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_059`. -/
@[expose]
noncomputable def nb062AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_060`. -/
@[expose]
noncomputable def nb062AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_061`. -/
@[expose]
noncomputable def nb062AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_062`. -/
@[expose]
noncomputable def nb062AlphaDummy062 : Var :=
  (freshVar (((synCnin (Class.cv (nb062AlphaDummy057))
          (Class.cv (nb062AlphaDummy058)))).fv ∪
      ((synCnin (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_063`. -/
@[expose]
noncomputable def nb062AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb062AlphaDummy060 x y))
          (Class.cv (nb062AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb062AlphaDummy060 x y))
          (Class.cv (nb062AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_064`. -/
@[expose]
noncomputable def nb062AlphaDummy064 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_065`. -/
@[expose]
noncomputable def nb062AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb062AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_066`. -/
@[expose]
noncomputable def nb062AlphaDummy066 : Var :=
  (freshVar (((synCcompl (Class.cv (nb062AlphaDummy057)))).fv ∪
      ((synCcompl (Class.cv (nb062AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_067`. -/
@[expose]
noncomputable def nb062AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb062AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb062AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_068`. -/
@[expose]
noncomputable def nb062AlphaDummy068 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_069`. -/
@[expose]
noncomputable def nb062AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb062AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_070`. -/
@[expose]
noncomputable def nb062AlphaDummy070 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy058))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_071`. -/
@[expose]
noncomputable def nb062AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb062AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_072`. -/
@[expose]
noncomputable def nb062AlphaDummy072 : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy042)
          (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
            (Wff.classEq (Class.cv (nb062AlphaDummy042))
              (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy042)
          (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
            (Wff.classEq (Class.cv (nb062AlphaDummy042))
              (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_073`. -/
@[expose]
noncomputable def nb062AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy044 x y)
          (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
              (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy044 x y)
          (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
              (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_074`. -/
@[expose]
noncomputable def nb062AlphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb062AlphaDummy043))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_075`. -/
@[expose]
noncomputable def nb062AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb062AlphaDummy045 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_076`. -/
@[expose]
noncomputable def nb062AlphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv (nb062AlphaDummy043)))).fv ∪
      ((synCphi (Class.cv (nb062AlphaDummy043)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_077`. -/
@[expose]
noncomputable def nb062AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb062AlphaDummy045 x y)))).fv ∪
      ((synCphi (Class.cv (nb062AlphaDummy045 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_078`. -/
@[expose]
noncomputable def nb062AlphaDummy078 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_079`. -/
@[expose]
noncomputable def nb062AlphaDummy079 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_080`. -/
@[expose]
noncomputable def nb062AlphaDummy080 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_081`. -/
@[expose]
noncomputable def nb062AlphaDummy081 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_082`. -/
@[expose]
noncomputable def nb062AlphaDummy082 : Var :=
  (freshVar (((synCcompl (Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCphi (Class.cv (nb062AlphaDummy079)))))))).fv ∪ ((synCcompl
          (Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_083`. -/
@[expose]
noncomputable def nb062AlphaDummy083 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCphi (Class.cv (nb062AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_084`. -/
@[expose]
noncomputable def nb062AlphaDummy084 : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy078)
          (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
            (Wff.classEq (Class.cv (nb062AlphaDummy078))
              (synCphi (Class.cv (nb062AlphaDummy079))))))).fv ∪
      ((Class.cab (nb062AlphaDummy078)
          (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
            (Wff.classEq (Class.cv (nb062AlphaDummy078))
              (synCphi (Class.cv (nb062AlphaDummy079))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_085`. -/
@[expose]
noncomputable def nb062AlphaDummy085 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy080 x y)
          (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
              (synCphi (Class.cv (nb062AlphaDummy081 x y))))))).fv ∪
      ((Class.cab (nb062AlphaDummy080 x y) (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
              (synCphi (Class.cv (nb062AlphaDummy081 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_086`. -/
@[expose]
noncomputable def nb062AlphaDummy086 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy079))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_087`. -/
@[expose]
noncomputable def nb062AlphaDummy087 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy079))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_088`. -/
@[expose]
noncomputable def nb062AlphaDummy088 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy081 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_089`. -/
@[expose]
noncomputable def nb062AlphaDummy089 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy081 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_090`. -/
@[expose]
noncomputable def nb062AlphaDummy090 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062AlphaDummy086)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb062AlphaDummy086)) (synC1c))).fv ∪
      ((Class.cv (nb062AlphaDummy086))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_091`. -/
@[expose]
noncomputable def nb062AlphaDummy091 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb062AlphaDummy088 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb062AlphaDummy088 x y)) (synC1c))).fv ∪
      ((Class.cv (nb062AlphaDummy088 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_092`. -/
@[expose]
noncomputable def nb062AlphaDummy092 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_093`. -/
@[expose]
noncomputable def nb062AlphaDummy093 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_094`. -/
@[expose]
noncomputable def nb062AlphaDummy094 : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_095`. -/
@[expose]
noncomputable def nb062AlphaDummy095 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_096`. -/
@[expose]
noncomputable def nb062AlphaDummy096 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_097`. -/
@[expose]
noncomputable def nb062AlphaDummy097 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_098`. -/
@[expose]
noncomputable def nb062AlphaDummy098 : Var :=
  (freshVar (((synCnin (Class.cv (nb062AlphaDummy093))
          (Class.cv (nb062AlphaDummy094)))).fv ∪
      ((synCnin (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_099`. -/
@[expose]
noncomputable def nb062AlphaDummy099 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb062AlphaDummy096 x y))
          (Class.cv (nb062AlphaDummy097 x y)))).fv ∪
      ((synCnin (Class.cv (nb062AlphaDummy096 x y))
          (Class.cv (nb062AlphaDummy097 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_100`. -/
@[expose]
noncomputable def nb062AlphaDummy100 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_101`. -/
@[expose]
noncomputable def nb062AlphaDummy101 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
      ((Class.cv (nb062AlphaDummy097 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_102`. -/
@[expose]
noncomputable def nb062AlphaDummy102 : Var :=
  (freshVar (((synCcompl (Class.cv (nb062AlphaDummy093)))).fv ∪
      ((synCcompl (Class.cv (nb062AlphaDummy094)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_103`. -/
@[expose]
noncomputable def nb062AlphaDummy103 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb062AlphaDummy096 x y)))).fv ∪
      ((synCcompl (Class.cv (nb062AlphaDummy097 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_104`. -/
@[expose]
noncomputable def nb062AlphaDummy104 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy093))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_105`. -/
@[expose]
noncomputable def nb062AlphaDummy105 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
      ((Class.cv (nb062AlphaDummy096 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_106`. -/
@[expose]
noncomputable def nb062AlphaDummy106 : Var :=
  (freshVar
    (((Class.cv (nb062AlphaDummy094))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_107`. -/
@[expose]
noncomputable def nb062AlphaDummy107 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb062AlphaDummy097 x y))).fv ∪
      ((Class.cv (nb062AlphaDummy097 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_108`. -/
@[expose]
noncomputable def nb062AlphaDummy108 : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy078)
          (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
            (Wff.classEq (Class.cv (nb062AlphaDummy078))
              (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy078)
          (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
            (Wff.classEq (Class.cv (nb062AlphaDummy078))
              (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_109`. -/
@[expose]
noncomputable def nb062AlphaDummy109 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb062AlphaDummy080 x y)
          (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
              (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy080 x y)
          (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
              (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_110`. -/
@[expose]
noncomputable def nb062AlphaDummy110 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb062AlphaDummy079))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_111`. -/
@[expose]
noncomputable def nb062AlphaDummy111 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb062AlphaDummy081 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_112`. -/
@[expose]
noncomputable def nb062AlphaDummy112 : Var :=
  (freshVar (((synCphi (Class.cv (nb062AlphaDummy079)))).fv ∪
      ((synCphi (Class.cv (nb062AlphaDummy079)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb062_alpha_dummy_113`. -/
@[expose]
noncomputable def nb062AlphaDummy113 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb062AlphaDummy081 x y)))).fv ∪
      ((synCphi (Class.cv (nb062AlphaDummy081 x y)))).fv) 0)

theorem nb062_fresh_000 :
    (nb062AlphaDummy036) ∉
      (((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb062AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb062_fresh_001 :
    (nb062AlphaDummy012) ∉
      (((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCphi (Class.cv (nb062AlphaDummy007))))))).fv ∪
        ((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCphi (Class.cv (nb062AlphaDummy007))))))).fv) :=
  by
  simpa only [nb062AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCphi (Class.cv (nb062AlphaDummy007))))))).fv ∪
        ((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCphi (Class.cv (nb062AlphaDummy007))))))).fv)
      0

theorem nb062_fresh_002 (r : Var) (a : Var) :
    (nb062AlphaDummy037 r a) ∉
      (((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb062AlphaDummy037] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb062_fresh_003 (r : Var) (a : Var) :
    (nb062AlphaDummy013 r a) ∉
      (((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCphi (Class.cv (nb062AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCphi (Class.cv (nb062AlphaDummy009 r a))))))).fv) :=
  by
  simpa only [nb062AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCphi (Class.cv (nb062AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCphi (Class.cv (nb062AlphaDummy009 r a))))))).fv)
      0

theorem nb062_fresh_004 :
    (nb062AlphaDummy048) ∉
      (((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCphi (Class.cv (nb062AlphaDummy043))))))).fv ∪
        ((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCphi (Class.cv (nb062AlphaDummy043))))))).fv) :=
  by
  simpa only [nb062AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCphi (Class.cv (nb062AlphaDummy043))))))).fv ∪
        ((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCphi (Class.cv (nb062AlphaDummy043))))))).fv)
      0

theorem nb062_fresh_005 :
    (nb062AlphaDummy072) ∉
      (((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb062AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb062_fresh_006 (x : Var) (y : Var) :
    (nb062AlphaDummy049 x y) ∉
      (((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCphi (Class.cv (nb062AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCphi (Class.cv (nb062AlphaDummy045 x y))))))).fv) :=
  by
  simpa only [nb062AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCphi (Class.cv (nb062AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCphi (Class.cv (nb062AlphaDummy045 x y))))))).fv)
      0

theorem nb062_fresh_007 (x : Var) (y : Var) :
    (nb062AlphaDummy073 x y) ∉
      (((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb062AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb062_fresh_008 :
    (nb062AlphaDummy108) ∉
      (((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb062AlphaDummy108] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb062_fresh_009 :
    (nb062AlphaDummy084) ∉
      (((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCphi (Class.cv (nb062AlphaDummy079))))))).fv ∪
        ((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCphi (Class.cv (nb062AlphaDummy079))))))).fv) :=
  by
  simpa only [nb062AlphaDummy084] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCphi (Class.cv (nb062AlphaDummy079))))))).fv ∪
        ((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCphi (Class.cv (nb062AlphaDummy079))))))).fv)
      0

theorem nb062_fresh_010 (x : Var) (y : Var) :
    (nb062AlphaDummy109 x y) ∉
      (((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb062AlphaDummy109] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb062_fresh_011 (x : Var) (y : Var) :
    (nb062AlphaDummy085 x y) ∉
      (((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCphi (Class.cv (nb062AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCphi (Class.cv (nb062AlphaDummy081 x y))))))).fv) :=
  by
  simpa only [nb062AlphaDummy085] using
    freshVar_not_mem
      (((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCphi (Class.cv (nb062AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCphi (Class.cv (nb062AlphaDummy081 x y))))))).fv)
      0

theorem nb062_fresh_012 :
    (nb062AlphaDummy006) ∉
      (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv) :=
  by
  simpa only [nb062AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv)
      0

theorem nb062_fresh_013 :
    (nb062AlphaDummy007) ∉
      (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv) :=
  by
  simpa only [nb062AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv)
      1

theorem nb062_distinct_014 : (nb062AlphaDummy006) ≠ (nb062AlphaDummy007) := by
  simpa only [nb062AlphaDummy006, nb062AlphaDummy007] using
    (freshVar_injective
      (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_fresh_015 :
    (nb062AlphaDummy042) ∉
      (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv) :=
  by
  simpa only [nb062AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv)
      0

theorem nb062_fresh_016 :
    (nb062AlphaDummy043) ∉
      (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv) :=
  by
  simpa only [nb062AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv)
      1

theorem nb062_distinct_017 : (nb062AlphaDummy042) ≠ (nb062AlphaDummy043) := by
  simpa only [nb062AlphaDummy042, nb062AlphaDummy043] using
    (freshVar_injective
      (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_fresh_018 :
    (nb062AlphaDummy078) ∉
      (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv) :=
  by
  simpa only [nb062AlphaDummy078] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv)
      0

theorem nb062_fresh_019 :
    (nb062AlphaDummy079) ∉
      (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv) :=
  by
  simpa only [nb062AlphaDummy079] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv)
      1

theorem nb062_distinct_020 : (nb062AlphaDummy078) ≠ (nb062AlphaDummy079) := by
  simpa only [nb062AlphaDummy078, nb062AlphaDummy079] using
    (freshVar_injective
      (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_fresh_021 :
    (nb062AlphaDummy014) ∉ (((Class.cv (nb062AlphaDummy007))).fv) := by
  simpa only [nb062AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy007))).fv) 0

theorem nb062_fresh_022 :
    (nb062AlphaDummy015) ∉ (((Class.cv (nb062AlphaDummy007))).fv) := by
  simpa only [nb062AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy007))).fv) 1

theorem nb062_distinct_023 : (nb062AlphaDummy014) ≠ (nb062AlphaDummy015) := by
  simpa only [nb062AlphaDummy014, nb062AlphaDummy015] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_024 (r : Var) (a : Var) :
    (nb062AlphaDummy016 r a) ∉ (((Class.cv (nb062AlphaDummy009 r a))).fv) := by
  simpa only [nb062AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy009 r a))).fv) 0

theorem nb062_fresh_025 (r : Var) (a : Var) :
    (nb062AlphaDummy017 r a) ∉ (((Class.cv (nb062AlphaDummy009 r a))).fv) := by
  simpa only [nb062AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy009 r a))).fv) 1

theorem nb062_distinct_026 (r : Var) (a : Var) :
    (nb062AlphaDummy016 r a) ≠ (nb062AlphaDummy017 r a) := by
  simpa only [nb062AlphaDummy016, nb062AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy009 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb062_fresh_027 :
    (nb062AlphaDummy020) ∉
      (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) 0

theorem nb062_fresh_028 :
    (nb062AlphaDummy021) ∉
      (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) 1

theorem nb062_fresh_029 :
    (nb062AlphaDummy022) ∉
      (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) 2

theorem nb062_distinct_030 : (nb062AlphaDummy020) ≠ (nb062AlphaDummy021) := by
  simpa only [nb062AlphaDummy020, nb062AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb062_distinct_031 : (nb062AlphaDummy020) ≠ (nb062AlphaDummy022) := by
  simpa only [nb062AlphaDummy020, nb062AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb062_distinct_032 : (nb062AlphaDummy021) ≠ (nb062AlphaDummy022) := by
  simpa only [nb062AlphaDummy021, nb062AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb062_fresh_033 (r : Var) (a : Var) :
    (nb062AlphaDummy023 r a) ∉
      (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 0

theorem nb062_fresh_034 (r : Var) (a : Var) :
    (nb062AlphaDummy024 r a) ∉
      (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 1

theorem nb062_fresh_035 (r : Var) (a : Var) :
    (nb062AlphaDummy025 r a) ∉
      (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 2

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C062C001Part002`. -/


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

theorem nb062_distinct_036 (r : Var) (a : Var) :
    (nb062AlphaDummy023 r a) ≠ (nb062AlphaDummy024 r a) := by
  simpa only [nb062AlphaDummy023, nb062AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_distinct_037 (r : Var) (a : Var) :
    (nb062AlphaDummy023 r a) ≠ (nb062AlphaDummy025 r a) := by
  simpa only [nb062AlphaDummy023, nb062AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb062_distinct_038 (r : Var) (a : Var) :
    (nb062AlphaDummy024 r a) ≠ (nb062AlphaDummy025 r a) := by
  simpa only [nb062AlphaDummy024, nb062AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb062_fresh_039 :
    (nb062AlphaDummy032) ∉
      (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy021))).fv) :=
  by
  simpa only [nb062AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy021))).fv)
      0

theorem nb062_fresh_040 :
    (nb062AlphaDummy028) ∉
      (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv) :=
  by
  simpa only [nb062AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv)
      0

theorem nb062_fresh_041 :
    (nb062AlphaDummy034) ∉
      (((Class.cv (nb062AlphaDummy022))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv) :=
  by
  simpa only [nb062AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy022))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv)
      0

theorem nb062_fresh_042 (r : Var) (a : Var) :
    (nb062AlphaDummy033 r a) ∉
      (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy024 r a))).fv) :=
  by
  simpa only [nb062AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy024 r a))).fv)
      0

theorem nb062_fresh_043 (r : Var) (a : Var) :
    (nb062AlphaDummy029 r a) ∉
      (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy025 r a))).fv) :=
  by
  simpa only [nb062AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy025 r a))).fv)
      0

theorem nb062_fresh_044 (r : Var) (a : Var) :
    (nb062AlphaDummy035 r a) ∉
      (((Class.cv (nb062AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy025 r a))).fv) :=
  by
  simpa only [nb062AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy025 r a))).fv)
      0

theorem nb062_fresh_045 :
    (nb062AlphaDummy050) ∉ (((Class.cv (nb062AlphaDummy043))).fv) := by
  simpa only [nb062AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy043))).fv) 0

theorem nb062_fresh_046 :
    (nb062AlphaDummy051) ∉ (((Class.cv (nb062AlphaDummy043))).fv) := by
  simpa only [nb062AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy043))).fv) 1

theorem nb062_distinct_047 : (nb062AlphaDummy050) ≠ (nb062AlphaDummy051) := by
  simpa only [nb062AlphaDummy050, nb062AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy043))).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_048 (x : Var) (y : Var) :
    (nb062AlphaDummy052 x y) ∉ (((Class.cv (nb062AlphaDummy045 x y))).fv) := by
  simpa only [nb062AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy045 x y))).fv) 0

theorem nb062_fresh_049 (x : Var) (y : Var) :
    (nb062AlphaDummy053 x y) ∉ (((Class.cv (nb062AlphaDummy045 x y))).fv) := by
  simpa only [nb062AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy045 x y))).fv) 1

theorem nb062_distinct_050 (x : Var) (y : Var) :
    (nb062AlphaDummy052 x y) ≠ (nb062AlphaDummy053 x y) := by
  simpa only [nb062AlphaDummy052, nb062AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy045 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb062_fresh_051 :
    (nb062AlphaDummy056) ∉
      (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) 0

theorem nb062_fresh_052 :
    (nb062AlphaDummy057) ∉
      (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) 1

theorem nb062_fresh_053 :
    (nb062AlphaDummy058) ∉
      (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) 2

theorem nb062_distinct_054 : (nb062AlphaDummy056) ≠ (nb062AlphaDummy057) := by
  simpa only [nb062AlphaDummy056, nb062AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb062_distinct_055 : (nb062AlphaDummy056) ≠ (nb062AlphaDummy058) := by
  simpa only [nb062AlphaDummy056, nb062AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb062_distinct_056 : (nb062AlphaDummy057) ≠ (nb062AlphaDummy058) := by
  simpa only [nb062AlphaDummy057, nb062AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb062_fresh_057 (x : Var) (y : Var) :
    (nb062AlphaDummy059 x y) ∉
      (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb062_fresh_058 (x : Var) (y : Var) :
    (nb062AlphaDummy060 x y) ∉
      (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb062_fresh_059 (x : Var) (y : Var) :
    (nb062AlphaDummy061 x y) ∉
      (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb062_distinct_060 (x : Var) (y : Var) :
    (nb062AlphaDummy059 x y) ≠ (nb062AlphaDummy060 x y) := by
  simpa only [nb062AlphaDummy059, nb062AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_distinct_061 (x : Var) (y : Var) :
    (nb062AlphaDummy059 x y) ≠ (nb062AlphaDummy061 x y) := by
  simpa only [nb062AlphaDummy059, nb062AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb062_distinct_062 (x : Var) (y : Var) :
    (nb062AlphaDummy060 x y) ≠ (nb062AlphaDummy061 x y) := by
  simpa only [nb062AlphaDummy060, nb062AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb062_fresh_063 :
    (nb062AlphaDummy068) ∉
      (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy057))).fv) :=
  by
  simpa only [nb062AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy057))).fv)
      0

theorem nb062_fresh_064 :
    (nb062AlphaDummy064) ∉
      (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv) :=
  by
  simpa only [nb062AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv)
      0

theorem nb062_fresh_065 :
    (nb062AlphaDummy070) ∉
      (((Class.cv (nb062AlphaDummy058))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv) :=
  by
  simpa only [nb062AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy058))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv)
      0

theorem nb062_fresh_066 (x : Var) (y : Var) :
    (nb062AlphaDummy069 x y) ∉
      (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb062AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy060 x y))).fv)
      0

theorem nb062_fresh_067 (x : Var) (y : Var) :
    (nb062AlphaDummy065 x y) ∉
      (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb062AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy061 x y))).fv)
      0

theorem nb062_fresh_068 (x : Var) (y : Var) :
    (nb062AlphaDummy071 x y) ∉
      (((Class.cv (nb062AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb062AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy061 x y))).fv)
      0

theorem nb062_fresh_069 :
    (nb062AlphaDummy086) ∉ (((Class.cv (nb062AlphaDummy079))).fv) := by
  simpa only [nb062AlphaDummy086] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy079))).fv) 0

theorem nb062_fresh_070 :
    (nb062AlphaDummy087) ∉ (((Class.cv (nb062AlphaDummy079))).fv) := by
  simpa only [nb062AlphaDummy087] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy079))).fv) 1

theorem nb062_distinct_071 : (nb062AlphaDummy086) ≠ (nb062AlphaDummy087) := by
  simpa only [nb062AlphaDummy086, nb062AlphaDummy087] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy079))).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_072 (x : Var) (y : Var) :
    (nb062AlphaDummy088 x y) ∉ (((Class.cv (nb062AlphaDummy081 x y))).fv) := by
  simpa only [nb062AlphaDummy088] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy081 x y))).fv) 0

theorem nb062_fresh_073 (x : Var) (y : Var) :
    (nb062AlphaDummy089 x y) ∉ (((Class.cv (nb062AlphaDummy081 x y))).fv) := by
  simpa only [nb062AlphaDummy089] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy081 x y))).fv) 1

theorem nb062_distinct_074 (x : Var) (y : Var) :
    (nb062AlphaDummy088 x y) ≠ (nb062AlphaDummy089 x y) := by
  simpa only [nb062AlphaDummy088, nb062AlphaDummy089] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy081 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb062_fresh_075 :
    (nb062AlphaDummy092) ∉
      (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy092] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) 0

theorem nb062_fresh_076 :
    (nb062AlphaDummy093) ∉
      (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy093] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) 1

theorem nb062_fresh_077 :
    (nb062AlphaDummy094) ∉
      (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy094] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) 2

theorem nb062_distinct_078 : (nb062AlphaDummy092) ≠ (nb062AlphaDummy093) := by
  simpa only [nb062AlphaDummy092, nb062AlphaDummy093] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb062_distinct_079 : (nb062AlphaDummy092) ≠ (nb062AlphaDummy094) := by
  simpa only [nb062AlphaDummy092, nb062AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb062_distinct_080 : (nb062AlphaDummy093) ≠ (nb062AlphaDummy094) := by
  simpa only [nb062AlphaDummy093, nb062AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb062_fresh_081 (x : Var) (y : Var) :
    (nb062AlphaDummy095 x y) ∉
      (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy095] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb062_fresh_082 (x : Var) (y : Var) :
    (nb062AlphaDummy096 x y) ∉
      (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb062_fresh_083 (x : Var) (y : Var) :
    (nb062AlphaDummy097 x y) ∉
      (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb062AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb062_distinct_084 (x : Var) (y : Var) :
    (nb062AlphaDummy095 x y) ≠ (nb062AlphaDummy096 x y) := by
  simpa only [nb062AlphaDummy095, nb062AlphaDummy096] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb062_distinct_085 (x : Var) (y : Var) :
    (nb062AlphaDummy095 x y) ≠ (nb062AlphaDummy097 x y) := by
  simpa only [nb062AlphaDummy095, nb062AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb062_distinct_086 (x : Var) (y : Var) :
    (nb062AlphaDummy096 x y) ≠ (nb062AlphaDummy097 x y) := by
  simpa only [nb062AlphaDummy096, nb062AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb062_fresh_087 :
    (nb062AlphaDummy104) ∉
      (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy093))).fv) :=
  by
  simpa only [nb062AlphaDummy104] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy093))).fv)
      0

theorem nb062_fresh_088 :
    (nb062AlphaDummy100) ∉
      (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv) :=
  by
  simpa only [nb062AlphaDummy100] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv)
      0

theorem nb062_fresh_089 :
    (nb062AlphaDummy106) ∉
      (((Class.cv (nb062AlphaDummy094))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv) :=
  by
  simpa only [nb062AlphaDummy106] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy094))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv)
      0

theorem nb062_fresh_090 (x : Var) (y : Var) :
    (nb062AlphaDummy105 x y) ∉
      (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy096 x y))).fv) :=
  by
  simpa only [nb062AlphaDummy105] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy096 x y))).fv)
      0

theorem nb062_fresh_091 (x : Var) (y : Var) :
    (nb062AlphaDummy101 x y) ∉
      (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy097 x y))).fv) :=
  by
  simpa only [nb062AlphaDummy101] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy097 x y))).fv)
      0

theorem nb062_fresh_092 (x : Var) (y : Var) :
    (nb062AlphaDummy107 x y) ∉
      (((Class.cv (nb062AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy097 x y))).fv) :=
  by
  simpa only [nb062AlphaDummy107] using
    freshVar_not_mem
      (((Class.cv (nb062AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy097 x y))).fv)
      0

theorem nb062_fresh_093 (r : Var) (a : Var) :
    (nb062AlphaDummy008 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb062AlphaDummy008] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb062_fresh_094 (r : Var) (a : Var) :
    (nb062AlphaDummy009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb062AlphaDummy009] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb062_distinct_095 (r : Var) (a : Var) :
    (nb062AlphaDummy008 r a) ≠ (nb062AlphaDummy009 r a) := by
  simpa only [nb062AlphaDummy008, nb062AlphaDummy009] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_096 (x : Var) (y : Var) :
    (nb062AlphaDummy044 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb062AlphaDummy044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb062_fresh_097 (x : Var) (y : Var) :
    (nb062AlphaDummy045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb062AlphaDummy045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb062_distinct_098 (x : Var) (y : Var) :
    (nb062AlphaDummy044 x y) ≠ (nb062AlphaDummy045 x y) := by
  simpa only [nb062AlphaDummy044, nb062AlphaDummy045] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_099 (x : Var) (y : Var) :
    (nb062AlphaDummy080 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb062AlphaDummy080] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0

theorem nb062_fresh_100 (x : Var) (y : Var) :
    (nb062AlphaDummy081 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb062AlphaDummy081] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1

theorem nb062_distinct_101 (x : Var) (y : Var) :
    (nb062AlphaDummy080 x y) ≠ (nb062AlphaDummy081 x y) := by
  simpa only [nb062AlphaDummy080, nb062AlphaDummy081] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb062_fresh_102 :
    (nb062AlphaDummy018) ∉
      (((Wff.classMem (Class.cv (nb062AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy014))).fv) :=
  by
  simpa only [nb062AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy014))).fv)
      0

theorem nb062_fresh_103 (r : Var) (a : Var) :
    (nb062AlphaDummy019 r a) ∉
      (((Wff.classMem (Class.cv (nb062AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy016 r a))).fv) :=
  by
  simpa only [nb062AlphaDummy019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy016 r a))).fv)
      0

theorem nb062_fresh_104 :
    (nb062AlphaDummy054) ∉
      (((Wff.classMem (Class.cv (nb062AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy050))).fv) :=
  by
  simpa only [nb062AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy050))).fv)
      0

theorem nb062_fresh_105 (x : Var) (y : Var) :
    (nb062AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb062AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb062AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy052 x y))).fv)
      0

theorem nb062_fresh_106 :
    (nb062AlphaDummy090) ∉
      (((Wff.classMem (Class.cv (nb062AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy086))).fv) :=
  by
  simpa only [nb062AlphaDummy090] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy086))).fv)
      0

theorem nb062_fresh_107 (x : Var) (y : Var) :
    (nb062AlphaDummy091 x y) ∉
      (((Wff.classMem (Class.cv (nb062AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy088 x y))).fv) :=
  by
  simpa only [nb062AlphaDummy091] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb062AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy088 x y))).fv)
      0

theorem nb062_fresh_108 :
    (nb062AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb062AlphaDummy006)
              (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
                (Wff.classEq (Class.cv (nb062AlphaDummy006))
                  (synCphi (Class.cv (nb062AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy006)
              (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
                (Wff.classEq (Class.cv (nb062AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb062AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb062AlphaDummy006)
              (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
                (Wff.classEq (Class.cv (nb062AlphaDummy006))
                  (synCphi (Class.cv (nb062AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy006)
              (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
                (Wff.classEq (Class.cv (nb062AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb062_fresh_109 (r : Var) (a : Var) :
    (nb062AlphaDummy011 r a) ∉
      (((synCcompl (Class.cab (nb062AlphaDummy008 r a)
              (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                  (synCphi (Class.cv (nb062AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy008 r a)
              (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb062AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb062AlphaDummy008 r a)
              (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                  (synCphi (Class.cv (nb062AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy008 r a)
              (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb062_fresh_110 :
    (nb062AlphaDummy046) ∉
      (((synCcompl (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCphi (Class.cv (nb062AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb062AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCphi (Class.cv (nb062AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb062_fresh_111 (x : Var) (y : Var) :
    (nb062AlphaDummy047 x y) ∉
      (((synCcompl (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCphi (Class.cv (nb062AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb062AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCphi (Class.cv (nb062AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb062_fresh_112 :
    (nb062AlphaDummy082) ∉
      (((synCcompl (Class.cab (nb062AlphaDummy078)
              (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
                (Wff.classEq (Class.cv (nb062AlphaDummy078))
                  (synCphi (Class.cv (nb062AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy078)
              (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb062AlphaDummy082] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb062AlphaDummy078)
              (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
                (Wff.classEq (Class.cv (nb062AlphaDummy078))
                  (synCphi (Class.cv (nb062AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy078)
              (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb062_fresh_113 (x : Var) (y : Var) :
    (nb062AlphaDummy083 x y) ∉
      (((synCcompl (Class.cab (nb062AlphaDummy080 x y)
              (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                  (synCphi (Class.cv (nb062AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy080 x y)
              (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb062AlphaDummy083] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb062AlphaDummy080 x y)
              (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                  (synCphi (Class.cv (nb062AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy080 x y)
              (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb062_fresh_114 :
    (nb062AlphaDummy030) ∉
      (((synCcompl (Class.cv (nb062AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy022)))).fv) :=
  by
  simpa only [nb062AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb062AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy022)))).fv)
      0

theorem nb062_fresh_115 (r : Var) (a : Var) :
    (nb062AlphaDummy031 r a) ∉
      (((synCcompl (Class.cv (nb062AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy025 r a)))).fv) :=
  by
  simpa only [nb062AlphaDummy031] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb062AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy025 r a)))).fv)
      0

theorem nb062_fresh_116 :
    (nb062AlphaDummy066) ∉
      (((synCcompl (Class.cv (nb062AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy058)))).fv) :=
  by
  simpa only [nb062AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb062AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy058)))).fv)
      0

theorem nb062_fresh_117 (x : Var) (y : Var) :
    (nb062AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb062AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb062AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb062AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy061 x y)))).fv)
      0

theorem nb062_fresh_118 :
    (nb062AlphaDummy102) ∉
      (((synCcompl (Class.cv (nb062AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy094)))).fv) :=
  by
  simpa only [nb062AlphaDummy102] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb062AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy094)))).fv)
      0

theorem nb062_fresh_119 (x : Var) (y : Var) :
    (nb062AlphaDummy103 x y) ∉
      (((synCcompl (Class.cv (nb062AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy097 x y)))).fv) :=
  by
  simpa only [nb062AlphaDummy103] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb062AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy097 x y)))).fv)
      0

theorem nb062_fresh_120 :
    (nb062AlphaDummy038) ∉
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb062AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb062_fresh_121 (r : Var) (a : Var) :
    (nb062AlphaDummy039 r a) ∉
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb062AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb062_fresh_122 :
    (nb062AlphaDummy074) ∉
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb062AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb062_fresh_123 (x : Var) (y : Var) :
    (nb062AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb062AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb062_fresh_124 :
    (nb062AlphaDummy110) ∉
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb062AlphaDummy110] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb062_fresh_125 (x : Var) (y : Var) :
    (nb062AlphaDummy111 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb062AlphaDummy111] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb062_fresh_126 :
    (nb062AlphaDummy026) ∉
      (((synCnin (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy021))
            (Class.cv (nb062AlphaDummy022)))).fv) :=
  by
  simpa only [nb062AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022)))).fv)
      0

theorem nb062_fresh_127 (r : Var) (a : Var) :
    (nb062AlphaDummy027 r a) ∉
      (((synCnin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a)))).fv) :=
  by
  simpa only [nb062AlphaDummy027] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a)))).fv)
      0

theorem nb062_fresh_128 :
    (nb062AlphaDummy062) ∉
      (((synCnin (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy057))
            (Class.cv (nb062AlphaDummy058)))).fv) :=
  by
  simpa only [nb062AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058)))).fv)
      0

theorem nb062_fresh_129 (x : Var) (y : Var) :
    (nb062AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb062AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y)))).fv)
      0

theorem nb062_fresh_130 :
    (nb062AlphaDummy098) ∉
      (((synCnin (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy093))
            (Class.cv (nb062AlphaDummy094)))).fv) :=
  by
  simpa only [nb062AlphaDummy098] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094)))).fv)
      0

theorem nb062_fresh_131 (x : Var) (y : Var) :
    (nb062AlphaDummy099 x y) ∉
      (((synCnin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y)))).fv) :=
  by
  simpa only [nb062AlphaDummy099] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y)))).fv)
      0

theorem nb062_fresh_132 :
    (nb062AlphaDummy040) ∉
      (((synCphi (Class.cv (nb062AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy007)))).fv) :=
  by
  simpa only [nb062AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb062AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy007)))).fv)
      0

theorem nb062_fresh_133 (r : Var) (a : Var) :
    (nb062AlphaDummy041 r a) ∉
      (((synCphi (Class.cv (nb062AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy009 r a)))).fv) :=
  by
  simpa only [nb062AlphaDummy041] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb062AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy009 r a)))).fv)
      0

theorem nb062_fresh_134 :
    (nb062AlphaDummy076) ∉
      (((synCphi (Class.cv (nb062AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy043)))).fv) :=
  by
  simpa only [nb062AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb062AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy043)))).fv)
      0

theorem nb062_fresh_135 (x : Var) (y : Var) :
    (nb062AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb062AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy045 x y)))).fv) :=
  by
  simpa only [nb062AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb062AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy045 x y)))).fv)
      0

theorem nb062_fresh_136 :
    (nb062AlphaDummy112) ∉
      (((synCphi (Class.cv (nb062AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy079)))).fv) :=
  by
  simpa only [nb062AlphaDummy112] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb062AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy079)))).fv)
      0

theorem nb062_fresh_137 (x : Var) (y : Var) :
    (nb062AlphaDummy113 x y) ∉
      (((synCphi (Class.cv (nb062AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy081 x y)))).fv) :=
  by
  simpa only [nb062AlphaDummy113] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb062AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy081 x y)))).fv)
      0

theorem nb062_fresh_138 :
    (nb062AlphaDummy004) ∉
      (({(nb062AlphaDummy001)} : Finset Var) ∪ ({(nb062AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb062AlphaDummy002) (Class.cv (nb062AlphaDummy000))
            (synWral (nb062AlphaDummy003) (Class.cv (nb062AlphaDummy000)) (Wff.imp
                (synWa (synWbr (Class.cv (nb062AlphaDummy002))
                    (Class.cv (nb062AlphaDummy001)) (Class.cv (nb062AlphaDummy003)))
                  (synWbr (Class.cv (nb062AlphaDummy003)) (Class.cv (nb062AlphaDummy001))
                    (Class.cv (nb062AlphaDummy002))))
                (Wff.objEq (nb062AlphaDummy002) (nb062AlphaDummy003)))))).fv) :=
  by
  simpa only [nb062AlphaDummy004] using
    freshVar_not_mem
      (({(nb062AlphaDummy001)} : Finset Var) ∪ ({(nb062AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb062AlphaDummy002) (Class.cv (nb062AlphaDummy000))
            (synWral (nb062AlphaDummy003) (Class.cv (nb062AlphaDummy000)) (Wff.imp
                (synWa (synWbr (Class.cv (nb062AlphaDummy002))
                    (Class.cv (nb062AlphaDummy001)) (Class.cv (nb062AlphaDummy003)))
                  (synWbr (Class.cv (nb062AlphaDummy003)) (Class.cv (nb062AlphaDummy001))
                    (Class.cv (nb062AlphaDummy002))))
                (Wff.objEq (nb062AlphaDummy002) (nb062AlphaDummy003)))))).fv)
      0

theorem nb062_fresh_139 (x : Var) (y : Var) (r : Var) (a : Var) :
    (nb062AlphaDummy005 x y r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (Wff.imp
                (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (synWbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv) :=
  by
  simpa only [nb062AlphaDummy005] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (Wff.imp
                (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (synWbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv)
      0

theorem nb062_fresh_140 : (nb062AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb062AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb062_fresh_141 : (nb062AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb062AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb062_fresh_142 : (nb062AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb062AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb062_fresh_143 : (nb062AlphaDummy003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb062AlphaDummy003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb062_distinct_144 : (nb062AlphaDummy000) ≠ (nb062AlphaDummy001) := by
  simpa only [nb062AlphaDummy000, nb062AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb062_distinct_145 : (nb062AlphaDummy000) ≠ (nb062AlphaDummy002) := by
  simpa only [nb062AlphaDummy000, nb062AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb062_distinct_146 : (nb062AlphaDummy000) ≠ (nb062AlphaDummy003) := by
  simpa only [nb062AlphaDummy000, nb062AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb062_distinct_147 : (nb062AlphaDummy001) ≠ (nb062AlphaDummy002) := by
  simpa only [nb062AlphaDummy001, nb062AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb062_distinct_148 : (nb062AlphaDummy001) ≠ (nb062AlphaDummy003) := by
  simpa only [nb062AlphaDummy001, nb062AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb062_distinct_149 : (nb062AlphaDummy002) ≠ (nb062AlphaDummy003) := by
  simpa only [nb062AlphaDummy002, nb062AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb062_support_mem_0000 :
    (nb062AlphaDummy001) ∈
      (({(nb062AlphaDummy001)} : Finset Var) ∪ ({(nb062AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb062AlphaDummy002) (Class.cv (nb062AlphaDummy000))
            (synWral (nb062AlphaDummy003) (Class.cv (nb062AlphaDummy000)) (Wff.imp
                (synWa (synWbr (Class.cv (nb062AlphaDummy002))
                    (Class.cv (nb062AlphaDummy001)) (Class.cv (nb062AlphaDummy003)))
                  (synWbr (Class.cv (nb062AlphaDummy003)) (Class.cv (nb062AlphaDummy001))
                    (Class.cv (nb062AlphaDummy002))))
                (Wff.objEq (nb062AlphaDummy002) (nb062AlphaDummy003)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0001 (x : Var) (y : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (Wff.imp
                (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (synWbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0002 :
    (nb062AlphaDummy000) ∈
      (({(nb062AlphaDummy001)} : Finset Var) ∪ ({(nb062AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb062AlphaDummy002) (Class.cv (nb062AlphaDummy000))
            (synWral (nb062AlphaDummy003) (Class.cv (nb062AlphaDummy000)) (Wff.imp
                (synWa (synWbr (Class.cv (nb062AlphaDummy002))
                    (Class.cv (nb062AlphaDummy001)) (Class.cv (nb062AlphaDummy003)))
                  (synWbr (Class.cv (nb062AlphaDummy003)) (Class.cv (nb062AlphaDummy001))
                    (Class.cv (nb062AlphaDummy002))))
                (Wff.objEq (nb062AlphaDummy002) (nb062AlphaDummy003)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0003 (x : Var) (y : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (Wff.imp
                (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (synWbr (Class.cv y) (Class.cv r) (Class.cv x))) (Wff.objEq x y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0004 :
    (nb062AlphaDummy001) ∈
      (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0005 :
    (nb062AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb062AlphaDummy006)
              (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
                (Wff.classEq (Class.cv (nb062AlphaDummy006))
                  (synCphi (Class.cv (nb062AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy006)
              (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
                (Wff.classEq (Class.cv (nb062AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((synCcompl (Class.cab (nb062AlphaDummy008 r a)
              (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                  (synCphi (Class.cv (nb062AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy008 r a)
              (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0008 :
    (nb062AlphaDummy001) ∈
      (((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCphi (Class.cv (nb062AlphaDummy007))))))).fv ∪
        ((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCphi (Class.cv (nb062AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCphi (Class.cv (nb062AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCphi (Class.cv (nb062AlphaDummy009 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0010 :
    (nb062AlphaDummy007) ∈ (((Class.cv (nb062AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0011 (r : Var) (a : Var) :
    (nb062AlphaDummy009 r a) ∈ (((Class.cv (nb062AlphaDummy009 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0012 :
    (nb062AlphaDummy014) ∈
      (((Wff.classMem (Class.cv (nb062AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy014))).fv) :=
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

theorem nb062_support_mem_0013 (r : Var) (a : Var) :
    (nb062AlphaDummy016 r a) ∈
      (((Wff.classMem (Class.cv (nb062AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy016 r a))).fv) :=
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

theorem nb062_support_mem_0014 :
    (nb062AlphaDummy014) ∈
      (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0015 (r : Var) (a : Var) :
    (nb062AlphaDummy016 r a) ∈
      (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0016 :
    (nb062AlphaDummy021) ∈
      (((synCnin (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy021))
            (Class.cv (nb062AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0017 (r : Var) (a : Var) :
    (nb062AlphaDummy024 r a) ∈
      (((synCnin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0018 :
    (nb062AlphaDummy021) ∈
      (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0019 (r : Var) (a : Var) :
    (nb062AlphaDummy024 r a) ∈
      (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0020 :
    (nb062AlphaDummy022) ∈
      (((synCnin (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy021))
            (Class.cv (nb062AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0021 (r : Var) (a : Var) :
    (nb062AlphaDummy025 r a) ∈
      (((synCnin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0022 :
    (nb062AlphaDummy022) ∈
      (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0023 (r : Var) (a : Var) :
    (nb062AlphaDummy025 r a) ∈
      (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0024 :
    (nb062AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0025 (r : Var) (a : Var) :
    (nb062AlphaDummy024 r a) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0026 :
    (nb062AlphaDummy021) ∈
      (((Class.cv (nb062AlphaDummy021))).fv ∪ ((Class.cv (nb062AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0027 (r : Var) (a : Var) :
    (nb062AlphaDummy024 r a) ∈
      (((Class.cv (nb062AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0028 :
    (nb062AlphaDummy022) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0029 (r : Var) (a : Var) :
    (nb062AlphaDummy025 r a) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0030 :
    (nb062AlphaDummy022) ∈
      (((Class.cv (nb062AlphaDummy022))).fv ∪ ((Class.cv (nb062AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0031 (r : Var) (a : Var) :
    (nb062AlphaDummy025 r a) ∈
      (((Class.cv (nb062AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb062AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0032 :
    (nb062AlphaDummy000) ∈
      (((Class.cv (nb062AlphaDummy001))).fv ∪ ((Class.cv (nb062AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0033 :
    (nb062AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb062AlphaDummy006)
              (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy001))
                (Wff.classEq (Class.cv (nb062AlphaDummy006))
                  (synCphi (Class.cv (nb062AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy006)
              (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
                (Wff.classEq (Class.cv (nb062AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((synCcompl (Class.cab (nb062AlphaDummy008 r a)
              (synWrex (nb062AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                  (synCphi (Class.cv (nb062AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy008 r a)
              (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C062C001Part003`. -/


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

theorem nb062_support_mem_0036 :
    (nb062AlphaDummy000) ∈
      (((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy006)
            (synWrex (nb062AlphaDummy007) (Class.cv (nb062AlphaDummy000))
              (Wff.classEq (Class.cv (nb062AlphaDummy006))
                (synCun (synCphi (Class.cv (nb062AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy008 r a)
            (synWrex (nb062AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb062AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0038 :
    (nb062AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0039 (r : Var) (a : Var) :
    (nb062AlphaDummy009 r a) ∈
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0040 :
    (nb062AlphaDummy007) ∈
      (((synCphi (Class.cv (nb062AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0041 (r : Var) (a : Var) :
    (nb062AlphaDummy009 r a) ∈
      (((synCphi (Class.cv (nb062AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy009 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0042 :
    (nb062AlphaDummy002) ∈
      (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0043 :
    (nb062AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCphi (Class.cv (nb062AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0044 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0045 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCphi (Class.cv (nb062AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0046 :
    (nb062AlphaDummy002) ∈
      (((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCphi (Class.cv (nb062AlphaDummy043))))))).fv ∪
        ((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCphi (Class.cv (nb062AlphaDummy043))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0047 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCphi (Class.cv (nb062AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCphi (Class.cv (nb062AlphaDummy045 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0048 :
    (nb062AlphaDummy043) ∈ (((Class.cv (nb062AlphaDummy043))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0049 (x : Var) (y : Var) :
    (nb062AlphaDummy045 x y) ∈ (((Class.cv (nb062AlphaDummy045 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0050 :
    (nb062AlphaDummy050) ∈
      (((Wff.classMem (Class.cv (nb062AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy050))).fv) :=
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

theorem nb062_support_mem_0051 (x : Var) (y : Var) :
    (nb062AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb062AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy052 x y))).fv) :=
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

theorem nb062_support_mem_0052 :
    (nb062AlphaDummy050) ∈
      (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0053 (x : Var) (y : Var) :
    (nb062AlphaDummy052 x y) ∈
      (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0054 :
    (nb062AlphaDummy057) ∈
      (((synCnin (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy057))
            (Class.cv (nb062AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0055 (x : Var) (y : Var) :
    (nb062AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0056 :
    (nb062AlphaDummy057) ∈
      (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0057 (x : Var) (y : Var) :
    (nb062AlphaDummy060 x y) ∈
      (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0058 :
    (nb062AlphaDummy058) ∈
      (((synCnin (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy057))
            (Class.cv (nb062AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0059 (x : Var) (y : Var) :
    (nb062AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0060 :
    (nb062AlphaDummy058) ∈
      (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0061 (x : Var) (y : Var) :
    (nb062AlphaDummy061 x y) ∈
      (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0062 :
    (nb062AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0063 (x : Var) (y : Var) :
    (nb062AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0064 :
    (nb062AlphaDummy057) ∈
      (((Class.cv (nb062AlphaDummy057))).fv ∪ ((Class.cv (nb062AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0065 (x : Var) (y : Var) :
    (nb062AlphaDummy060 x y) ∈
      (((Class.cv (nb062AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0066 :
    (nb062AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0067 (x : Var) (y : Var) :
    (nb062AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0068 :
    (nb062AlphaDummy058) ∈
      (((Class.cv (nb062AlphaDummy058))).fv ∪ ((Class.cv (nb062AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0069 (x : Var) (y : Var) :
    (nb062AlphaDummy061 x y) ∈
      (((Class.cv (nb062AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0070 :
    (nb062AlphaDummy003) ∈
      (((Class.cv (nb062AlphaDummy002))).fv ∪ ((Class.cv (nb062AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0071 :
    (nb062AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCphi (Class.cv (nb062AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0072 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0073 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCphi (Class.cv (nb062AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0074 :
    (nb062AlphaDummy003) ∈
      (((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy042)
            (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy042))
                (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0075 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy044 x y)
            (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0076 :
    (nb062AlphaDummy043) ∈
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0077 (x : Var) (y : Var) :
    (nb062AlphaDummy045 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0078 :
    (nb062AlphaDummy043) ∈
      (((synCphi (Class.cv (nb062AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy043)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0079 (x : Var) (y : Var) :
    (nb062AlphaDummy045 x y) ∈
      (((synCphi (Class.cv (nb062AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy045 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0080 :
    (nb062AlphaDummy003) ∈
      (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0081 :
    (nb062AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb062AlphaDummy078)
              (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
                (Wff.classEq (Class.cv (nb062AlphaDummy078))
                  (synCphi (Class.cv (nb062AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy078)
              (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0082 (x : Var) (y : Var) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0083 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb062AlphaDummy080 x y)
              (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                  (synCphi (Class.cv (nb062AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy080 x y)
              (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0084 :
    (nb062AlphaDummy003) ∈
      (((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCphi (Class.cv (nb062AlphaDummy079))))))).fv ∪
        ((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCphi (Class.cv (nb062AlphaDummy079))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0085 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCphi (Class.cv (nb062AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCphi (Class.cv (nb062AlphaDummy081 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0086 :
    (nb062AlphaDummy079) ∈ (((Class.cv (nb062AlphaDummy079))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0087 (x : Var) (y : Var) :
    (nb062AlphaDummy081 x y) ∈ (((Class.cv (nb062AlphaDummy081 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0088 :
    (nb062AlphaDummy086) ∈
      (((Wff.classMem (Class.cv (nb062AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy086))).fv) :=
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

theorem nb062_support_mem_0089 (x : Var) (y : Var) :
    (nb062AlphaDummy088 x y) ∈
      (((Wff.classMem (Class.cv (nb062AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb062AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb062AlphaDummy088 x y))).fv) :=
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

theorem nb062_support_mem_0090 :
    (nb062AlphaDummy086) ∈
      (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0091 (x : Var) (y : Var) :
    (nb062AlphaDummy088 x y) ∈
      (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0092 :
    (nb062AlphaDummy093) ∈
      (((synCnin (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy093))
            (Class.cv (nb062AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0093 (x : Var) (y : Var) :
    (nb062AlphaDummy096 x y) ∈
      (((synCnin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0094 :
    (nb062AlphaDummy093) ∈
      (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0095 (x : Var) (y : Var) :
    (nb062AlphaDummy096 x y) ∈
      (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0096 :
    (nb062AlphaDummy094) ∈
      (((synCnin (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy093))
            (Class.cv (nb062AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0097 (x : Var) (y : Var) :
    (nb062AlphaDummy097 x y) ∈
      (((synCnin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0098 :
    (nb062AlphaDummy094) ∈
      (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0099 (x : Var) (y : Var) :
    (nb062AlphaDummy097 x y) ∈
      (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0100 :
    (nb062AlphaDummy093) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0101 (x : Var) (y : Var) :
    (nb062AlphaDummy096 x y) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0102 :
    (nb062AlphaDummy093) ∈
      (((Class.cv (nb062AlphaDummy093))).fv ∪ ((Class.cv (nb062AlphaDummy093))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0103 (x : Var) (y : Var) :
    (nb062AlphaDummy096 x y) ∈
      (((Class.cv (nb062AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy096 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0104 :
    (nb062AlphaDummy094) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0105 (x : Var) (y : Var) :
    (nb062AlphaDummy097 x y) ∈
      (((synCcompl (Class.cv (nb062AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb062AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0106 :
    (nb062AlphaDummy094) ∈
      (((Class.cv (nb062AlphaDummy094))).fv ∪ ((Class.cv (nb062AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0107 (x : Var) (y : Var) :
    (nb062AlphaDummy097 x y) ∈
      (((Class.cv (nb062AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb062AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0108 :
    (nb062AlphaDummy002) ∈
      (((Class.cv (nb062AlphaDummy003))).fv ∪ ((Class.cv (nb062AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0109 :
    (nb062AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb062AlphaDummy078)
              (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy003))
                (Wff.classEq (Class.cv (nb062AlphaDummy078))
                  (synCphi (Class.cv (nb062AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy078)
              (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0110 (x : Var) (y : Var) :
    x ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0111 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb062AlphaDummy080 x y)
              (synWrex (nb062AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                  (synCphi (Class.cv (nb062AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb062AlphaDummy080 x y)
              (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0112 :
    (nb062AlphaDummy002) ∈
      (((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCun (synCphi (Class.cv (nb062AlphaDummy079)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0113 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb062_support_mem_0114 :
    (nb062AlphaDummy079) ∈
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0115 (x : Var) (y : Var) :
    (nb062AlphaDummy081 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb062AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0116 :
    (nb062AlphaDummy079) ∈
      (((synCphi (Class.cv (nb062AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy079)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb062_support_mem_0117 (x : Var) (y : Var) :
    (nb062AlphaDummy081 x y) ∈
      (((synCphi (Class.cv (nb062AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb062AlphaDummy081 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
