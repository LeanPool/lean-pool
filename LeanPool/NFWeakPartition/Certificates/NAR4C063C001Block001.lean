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

/-! Certificates from `NAR4C063C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_000`. -/
@[expose]
noncomputable def nb063AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_001`. -/
@[expose]
noncomputable def nb063AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_002`. -/
@[expose]
noncomputable def nb063AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_003`. -/
@[expose]
noncomputable def nb063AlphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_004`. -/
@[expose]
noncomputable def nb063AlphaDummy004 : Var :=
  (freshVar
    (({(nb063AlphaDummy001)} : Finset Var) ∪ ({(nb063AlphaDummy000)} : Finset Var) ∪
      ((synWral (nb063AlphaDummy002) (Class.cv (nb063AlphaDummy000))
          (synWral (nb063AlphaDummy003) (Class.cv (nb063AlphaDummy000)) (synWo
              (synWbr (Class.cv (nb063AlphaDummy002))
                (Class.cv (nb063AlphaDummy001)) (Class.cv (nb063AlphaDummy003)))
              (synWbr (Class.cv (nb063AlphaDummy003)) (Class.cv (nb063AlphaDummy001))
                (Class.cv (nb063AlphaDummy002))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_005`. -/
@[expose]
noncomputable def nb063AlphaDummy005 (x : Var) (y : Var) (r : Var) (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
          (synWral y (Class.cv a) (synWo (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
              (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_006`. -/
@[expose]
noncomputable def nb063AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_007`. -/
@[expose]
noncomputable def nb063AlphaDummy007 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_008`. -/
@[expose]
noncomputable def nb063AlphaDummy008 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_009`. -/
@[expose]
noncomputable def nb063AlphaDummy009 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_010`. -/
@[expose]
noncomputable def nb063AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCphi (Class.cv (nb063AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_011`. -/
@[expose]
noncomputable def nb063AlphaDummy011 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCphi (Class.cv (nb063AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
          (Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_012`. -/
@[expose]
noncomputable def nb063AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy006)
          (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
            (Wff.classEq (Class.cv (nb063AlphaDummy006))
              (synCphi (Class.cv (nb063AlphaDummy007))))))).fv ∪
      ((Class.cab (nb063AlphaDummy006)
          (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
            (Wff.classEq (Class.cv (nb063AlphaDummy006))
              (synCphi (Class.cv (nb063AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_013`. -/
@[expose]
noncomputable def nb063AlphaDummy013 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy008 r a)
          (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
              (synCphi (Class.cv (nb063AlphaDummy009 r a))))))).fv ∪
      ((Class.cab (nb063AlphaDummy008 r a) (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
              (synCphi (Class.cv (nb063AlphaDummy009 r a))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_014`. -/
@[expose]
noncomputable def nb063AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_015`. -/
@[expose]
noncomputable def nb063AlphaDummy015 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_016`. -/
@[expose]
noncomputable def nb063AlphaDummy016 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy009 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_017`. -/
@[expose]
noncomputable def nb063AlphaDummy017 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy009 r a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_018`. -/
@[expose]
noncomputable def nb063AlphaDummy018 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb063AlphaDummy014)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb063AlphaDummy014)) (synC1c))).fv ∪
      ((Class.cv (nb063AlphaDummy014))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_019`. -/
@[expose]
noncomputable def nb063AlphaDummy019 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb063AlphaDummy016 r a)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb063AlphaDummy016 r a)) (synC1c))).fv ∪
      ((Class.cv (nb063AlphaDummy016 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_020`. -/
@[expose]
noncomputable def nb063AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_021`. -/
@[expose]
noncomputable def nb063AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_022`. -/
@[expose]
noncomputable def nb063AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_023`. -/
@[expose]
noncomputable def nb063AlphaDummy023 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_024`. -/
@[expose]
noncomputable def nb063AlphaDummy024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_025`. -/
@[expose]
noncomputable def nb063AlphaDummy025 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_026`. -/
@[expose]
noncomputable def nb063AlphaDummy026 : Var :=
  (freshVar (((synCnin (Class.cv (nb063AlphaDummy021))
          (Class.cv (nb063AlphaDummy022)))).fv ∪
      ((synCnin (Class.cv (nb063AlphaDummy021)) (Class.cv (nb063AlphaDummy022)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_027`. -/
@[expose]
noncomputable def nb063AlphaDummy027 (r : Var) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb063AlphaDummy024 r a))
          (Class.cv (nb063AlphaDummy025 r a)))).fv ∪
      ((synCnin (Class.cv (nb063AlphaDummy024 r a))
          (Class.cv (nb063AlphaDummy025 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_028`. -/
@[expose]
noncomputable def nb063AlphaDummy028 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_029`. -/
@[expose]
noncomputable def nb063AlphaDummy029 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
      ((Class.cv (nb063AlphaDummy025 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_030`. -/
@[expose]
noncomputable def nb063AlphaDummy030 : Var :=
  (freshVar (((synCcompl (Class.cv (nb063AlphaDummy021)))).fv ∪
      ((synCcompl (Class.cv (nb063AlphaDummy022)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_031`. -/
@[expose]
noncomputable def nb063AlphaDummy031 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb063AlphaDummy024 r a)))).fv ∪
      ((synCcompl (Class.cv (nb063AlphaDummy025 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_032`. -/
@[expose]
noncomputable def nb063AlphaDummy032 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_033`. -/
@[expose]
noncomputable def nb063AlphaDummy033 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
      ((Class.cv (nb063AlphaDummy024 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_034`. -/
@[expose]
noncomputable def nb063AlphaDummy034 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy022))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_035`. -/
@[expose]
noncomputable def nb063AlphaDummy035 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy025 r a))).fv ∪
      ((Class.cv (nb063AlphaDummy025 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_036`. -/
@[expose]
noncomputable def nb063AlphaDummy036 : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy006)
          (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
            (Wff.classEq (Class.cv (nb063AlphaDummy006))
              (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy006)
          (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
            (Wff.classEq (Class.cv (nb063AlphaDummy006))
              (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_037`. -/
@[expose]
noncomputable def nb063AlphaDummy037 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy008 r a)
          (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
              (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy008 r a)
          (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
              (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_038`. -/
@[expose]
noncomputable def nb063AlphaDummy038 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb063AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_039`. -/
@[expose]
noncomputable def nb063AlphaDummy039 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb063AlphaDummy009 r a))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_040`. -/
@[expose]
noncomputable def nb063AlphaDummy040 : Var :=
  (freshVar (((synCphi (Class.cv (nb063AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb063AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_041`. -/
@[expose]
noncomputable def nb063AlphaDummy041 (r : Var) (a : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb063AlphaDummy009 r a)))).fv ∪
      ((synCphi (Class.cv (nb063AlphaDummy009 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_042`. -/
@[expose]
noncomputable def nb063AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_043`. -/
@[expose]
noncomputable def nb063AlphaDummy043 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_044`. -/
@[expose]
noncomputable def nb063AlphaDummy044 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_045`. -/
@[expose]
noncomputable def nb063AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_046`. -/
@[expose]
noncomputable def nb063AlphaDummy046 : Var :=
  (freshVar (((synCcompl (Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCphi (Class.cv (nb063AlphaDummy043)))))))).fv ∪ ((synCcompl
          (Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_047`. -/
@[expose]
noncomputable def nb063AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCphi (Class.cv (nb063AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_048`. -/
@[expose]
noncomputable def nb063AlphaDummy048 : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy042)
          (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
            (Wff.classEq (Class.cv (nb063AlphaDummy042))
              (synCphi (Class.cv (nb063AlphaDummy043))))))).fv ∪
      ((Class.cab (nb063AlphaDummy042)
          (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
            (Wff.classEq (Class.cv (nb063AlphaDummy042))
              (synCphi (Class.cv (nb063AlphaDummy043))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_049`. -/
@[expose]
noncomputable def nb063AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy044 x y)
          (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
              (synCphi (Class.cv (nb063AlphaDummy045 x y))))))).fv ∪
      ((Class.cab (nb063AlphaDummy044 x y) (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
              (synCphi (Class.cv (nb063AlphaDummy045 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_050`. -/
@[expose]
noncomputable def nb063AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy043))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_051`. -/
@[expose]
noncomputable def nb063AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy043))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_052`. -/
@[expose]
noncomputable def nb063AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy045 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_053`. -/
@[expose]
noncomputable def nb063AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy045 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_054`. -/
@[expose]
noncomputable def nb063AlphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb063AlphaDummy050)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb063AlphaDummy050)) (synC1c))).fv ∪
      ((Class.cv (nb063AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_055`. -/
@[expose]
noncomputable def nb063AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb063AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb063AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb063AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_056`. -/
@[expose]
noncomputable def nb063AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_057`. -/
@[expose]
noncomputable def nb063AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_058`. -/
@[expose]
noncomputable def nb063AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_059`. -/
@[expose]
noncomputable def nb063AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_060`. -/
@[expose]
noncomputable def nb063AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_061`. -/
@[expose]
noncomputable def nb063AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_062`. -/
@[expose]
noncomputable def nb063AlphaDummy062 : Var :=
  (freshVar (((synCnin (Class.cv (nb063AlphaDummy057))
          (Class.cv (nb063AlphaDummy058)))).fv ∪
      ((synCnin (Class.cv (nb063AlphaDummy057)) (Class.cv (nb063AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_063`. -/
@[expose]
noncomputable def nb063AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb063AlphaDummy060 x y))
          (Class.cv (nb063AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb063AlphaDummy060 x y))
          (Class.cv (nb063AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_064`. -/
@[expose]
noncomputable def nb063AlphaDummy064 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_065`. -/
@[expose]
noncomputable def nb063AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb063AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_066`. -/
@[expose]
noncomputable def nb063AlphaDummy066 : Var :=
  (freshVar (((synCcompl (Class.cv (nb063AlphaDummy057)))).fv ∪
      ((synCcompl (Class.cv (nb063AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_067`. -/
@[expose]
noncomputable def nb063AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb063AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb063AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_068`. -/
@[expose]
noncomputable def nb063AlphaDummy068 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_069`. -/
@[expose]
noncomputable def nb063AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb063AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_070`. -/
@[expose]
noncomputable def nb063AlphaDummy070 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy058))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_071`. -/
@[expose]
noncomputable def nb063AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb063AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_072`. -/
@[expose]
noncomputable def nb063AlphaDummy072 : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy042)
          (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
            (Wff.classEq (Class.cv (nb063AlphaDummy042))
              (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy042)
          (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
            (Wff.classEq (Class.cv (nb063AlphaDummy042))
              (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_073`. -/
@[expose]
noncomputable def nb063AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy044 x y)
          (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
              (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy044 x y)
          (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
              (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_074`. -/
@[expose]
noncomputable def nb063AlphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb063AlphaDummy043))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_075`. -/
@[expose]
noncomputable def nb063AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb063AlphaDummy045 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_076`. -/
@[expose]
noncomputable def nb063AlphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv (nb063AlphaDummy043)))).fv ∪
      ((synCphi (Class.cv (nb063AlphaDummy043)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_077`. -/
@[expose]
noncomputable def nb063AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb063AlphaDummy045 x y)))).fv ∪
      ((synCphi (Class.cv (nb063AlphaDummy045 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_078`. -/
@[expose]
noncomputable def nb063AlphaDummy078 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_079`. -/
@[expose]
noncomputable def nb063AlphaDummy079 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_080`. -/
@[expose]
noncomputable def nb063AlphaDummy080 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_081`. -/
@[expose]
noncomputable def nb063AlphaDummy081 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_082`. -/
@[expose]
noncomputable def nb063AlphaDummy082 : Var :=
  (freshVar (((synCcompl (Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCphi (Class.cv (nb063AlphaDummy079)))))))).fv ∪ ((synCcompl
          (Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_083`. -/
@[expose]
noncomputable def nb063AlphaDummy083 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCphi (Class.cv (nb063AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_084`. -/
@[expose]
noncomputable def nb063AlphaDummy084 : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy078)
          (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
            (Wff.classEq (Class.cv (nb063AlphaDummy078))
              (synCphi (Class.cv (nb063AlphaDummy079))))))).fv ∪
      ((Class.cab (nb063AlphaDummy078)
          (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
            (Wff.classEq (Class.cv (nb063AlphaDummy078))
              (synCphi (Class.cv (nb063AlphaDummy079))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_085`. -/
@[expose]
noncomputable def nb063AlphaDummy085 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy080 x y)
          (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
              (synCphi (Class.cv (nb063AlphaDummy081 x y))))))).fv ∪
      ((Class.cab (nb063AlphaDummy080 x y) (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
              (synCphi (Class.cv (nb063AlphaDummy081 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_086`. -/
@[expose]
noncomputable def nb063AlphaDummy086 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy079))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_087`. -/
@[expose]
noncomputable def nb063AlphaDummy087 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy079))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_088`. -/
@[expose]
noncomputable def nb063AlphaDummy088 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy081 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_089`. -/
@[expose]
noncomputable def nb063AlphaDummy089 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy081 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_090`. -/
@[expose]
noncomputable def nb063AlphaDummy090 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb063AlphaDummy086)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb063AlphaDummy086)) (synC1c))).fv ∪
      ((Class.cv (nb063AlphaDummy086))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_091`. -/
@[expose]
noncomputable def nb063AlphaDummy091 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb063AlphaDummy088 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb063AlphaDummy088 x y)) (synC1c))).fv ∪
      ((Class.cv (nb063AlphaDummy088 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_092`. -/
@[expose]
noncomputable def nb063AlphaDummy092 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_093`. -/
@[expose]
noncomputable def nb063AlphaDummy093 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_094`. -/
@[expose]
noncomputable def nb063AlphaDummy094 : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_095`. -/
@[expose]
noncomputable def nb063AlphaDummy095 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_096`. -/
@[expose]
noncomputable def nb063AlphaDummy096 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_097`. -/
@[expose]
noncomputable def nb063AlphaDummy097 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_098`. -/
@[expose]
noncomputable def nb063AlphaDummy098 : Var :=
  (freshVar (((synCnin (Class.cv (nb063AlphaDummy093))
          (Class.cv (nb063AlphaDummy094)))).fv ∪
      ((synCnin (Class.cv (nb063AlphaDummy093)) (Class.cv (nb063AlphaDummy094)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_099`. -/
@[expose]
noncomputable def nb063AlphaDummy099 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb063AlphaDummy096 x y))
          (Class.cv (nb063AlphaDummy097 x y)))).fv ∪
      ((synCnin (Class.cv (nb063AlphaDummy096 x y))
          (Class.cv (nb063AlphaDummy097 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_100`. -/
@[expose]
noncomputable def nb063AlphaDummy100 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_101`. -/
@[expose]
noncomputable def nb063AlphaDummy101 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
      ((Class.cv (nb063AlphaDummy097 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_102`. -/
@[expose]
noncomputable def nb063AlphaDummy102 : Var :=
  (freshVar (((synCcompl (Class.cv (nb063AlphaDummy093)))).fv ∪
      ((synCcompl (Class.cv (nb063AlphaDummy094)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_103`. -/
@[expose]
noncomputable def nb063AlphaDummy103 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb063AlphaDummy096 x y)))).fv ∪
      ((synCcompl (Class.cv (nb063AlphaDummy097 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_104`. -/
@[expose]
noncomputable def nb063AlphaDummy104 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy093))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_105`. -/
@[expose]
noncomputable def nb063AlphaDummy105 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
      ((Class.cv (nb063AlphaDummy096 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_106`. -/
@[expose]
noncomputable def nb063AlphaDummy106 : Var :=
  (freshVar
    (((Class.cv (nb063AlphaDummy094))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_107`. -/
@[expose]
noncomputable def nb063AlphaDummy107 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb063AlphaDummy097 x y))).fv ∪
      ((Class.cv (nb063AlphaDummy097 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_108`. -/
@[expose]
noncomputable def nb063AlphaDummy108 : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy078)
          (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
            (Wff.classEq (Class.cv (nb063AlphaDummy078))
              (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy078)
          (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
            (Wff.classEq (Class.cv (nb063AlphaDummy078))
              (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_109`. -/
@[expose]
noncomputable def nb063AlphaDummy109 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb063AlphaDummy080 x y)
          (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
              (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy080 x y)
          (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
              (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_110`. -/
@[expose]
noncomputable def nb063AlphaDummy110 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb063AlphaDummy079))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_111`. -/
@[expose]
noncomputable def nb063AlphaDummy111 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb063AlphaDummy081 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_112`. -/
@[expose]
noncomputable def nb063AlphaDummy112 : Var :=
  (freshVar (((synCphi (Class.cv (nb063AlphaDummy079)))).fv ∪
      ((synCphi (Class.cv (nb063AlphaDummy079)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb063_alpha_dummy_113`. -/
@[expose]
noncomputable def nb063AlphaDummy113 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb063AlphaDummy081 x y)))).fv ∪
      ((synCphi (Class.cv (nb063AlphaDummy081 x y)))).fv) 0)

theorem nb063_fresh_000 :
    (nb063AlphaDummy036) ∉
      (((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb063AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb063_fresh_001 :
    (nb063AlphaDummy012) ∉
      (((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCphi (Class.cv (nb063AlphaDummy007))))))).fv ∪
        ((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCphi (Class.cv (nb063AlphaDummy007))))))).fv) :=
  by
  simpa only [nb063AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCphi (Class.cv (nb063AlphaDummy007))))))).fv ∪
        ((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCphi (Class.cv (nb063AlphaDummy007))))))).fv)
      0

theorem nb063_fresh_002 (r : Var) (a : Var) :
    (nb063AlphaDummy037 r a) ∉
      (((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb063AlphaDummy037] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb063_fresh_003 (r : Var) (a : Var) :
    (nb063AlphaDummy013 r a) ∉
      (((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCphi (Class.cv (nb063AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCphi (Class.cv (nb063AlphaDummy009 r a))))))).fv) :=
  by
  simpa only [nb063AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCphi (Class.cv (nb063AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCphi (Class.cv (nb063AlphaDummy009 r a))))))).fv)
      0

theorem nb063_fresh_004 :
    (nb063AlphaDummy048) ∉
      (((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCphi (Class.cv (nb063AlphaDummy043))))))).fv ∪
        ((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCphi (Class.cv (nb063AlphaDummy043))))))).fv) :=
  by
  simpa only [nb063AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCphi (Class.cv (nb063AlphaDummy043))))))).fv ∪
        ((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCphi (Class.cv (nb063AlphaDummy043))))))).fv)
      0

theorem nb063_fresh_005 :
    (nb063AlphaDummy072) ∉
      (((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb063AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb063_fresh_006 (x : Var) (y : Var) :
    (nb063AlphaDummy049 x y) ∉
      (((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCphi (Class.cv (nb063AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCphi (Class.cv (nb063AlphaDummy045 x y))))))).fv) :=
  by
  simpa only [nb063AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCphi (Class.cv (nb063AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCphi (Class.cv (nb063AlphaDummy045 x y))))))).fv)
      0

theorem nb063_fresh_007 (x : Var) (y : Var) :
    (nb063AlphaDummy073 x y) ∉
      (((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb063AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb063_fresh_008 :
    (nb063AlphaDummy108) ∉
      (((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb063AlphaDummy108] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb063_fresh_009 :
    (nb063AlphaDummy084) ∉
      (((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCphi (Class.cv (nb063AlphaDummy079))))))).fv ∪
        ((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCphi (Class.cv (nb063AlphaDummy079))))))).fv) :=
  by
  simpa only [nb063AlphaDummy084] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCphi (Class.cv (nb063AlphaDummy079))))))).fv ∪
        ((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCphi (Class.cv (nb063AlphaDummy079))))))).fv)
      0

theorem nb063_fresh_010 (x : Var) (y : Var) :
    (nb063AlphaDummy109 x y) ∉
      (((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb063AlphaDummy109] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb063_fresh_011 (x : Var) (y : Var) :
    (nb063AlphaDummy085 x y) ∉
      (((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCphi (Class.cv (nb063AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCphi (Class.cv (nb063AlphaDummy081 x y))))))).fv) :=
  by
  simpa only [nb063AlphaDummy085] using
    freshVar_not_mem
      (((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCphi (Class.cv (nb063AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCphi (Class.cv (nb063AlphaDummy081 x y))))))).fv)
      0

theorem nb063_fresh_012 :
    (nb063AlphaDummy006) ∉
      (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv) :=
  by
  simpa only [nb063AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv)
      0

theorem nb063_fresh_013 :
    (nb063AlphaDummy007) ∉
      (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv) :=
  by
  simpa only [nb063AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv)
      1

theorem nb063_distinct_014 : (nb063AlphaDummy006) ≠ (nb063AlphaDummy007) := by
  simpa only [nb063AlphaDummy006, nb063AlphaDummy007] using
    (freshVar_injective
      (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb063_fresh_015 :
    (nb063AlphaDummy042) ∉
      (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv) :=
  by
  simpa only [nb063AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv)
      0

theorem nb063_fresh_016 :
    (nb063AlphaDummy043) ∉
      (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv) :=
  by
  simpa only [nb063AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv)
      1

theorem nb063_distinct_017 : (nb063AlphaDummy042) ≠ (nb063AlphaDummy043) := by
  simpa only [nb063AlphaDummy042, nb063AlphaDummy043] using
    (freshVar_injective
      (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb063_fresh_018 :
    (nb063AlphaDummy078) ∉
      (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv) :=
  by
  simpa only [nb063AlphaDummy078] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv)
      0

theorem nb063_fresh_019 :
    (nb063AlphaDummy079) ∉
      (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv) :=
  by
  simpa only [nb063AlphaDummy079] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv)
      1

theorem nb063_distinct_020 : (nb063AlphaDummy078) ≠ (nb063AlphaDummy079) := by
  simpa only [nb063AlphaDummy078, nb063AlphaDummy079] using
    (freshVar_injective
      (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb063_fresh_021 :
    (nb063AlphaDummy014) ∉ (((Class.cv (nb063AlphaDummy007))).fv) := by
  simpa only [nb063AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy007))).fv) 0

theorem nb063_fresh_022 :
    (nb063AlphaDummy015) ∉ (((Class.cv (nb063AlphaDummy007))).fv) := by
  simpa only [nb063AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy007))).fv) 1

theorem nb063_distinct_023 : (nb063AlphaDummy014) ≠ (nb063AlphaDummy015) := by
  simpa only [nb063AlphaDummy014, nb063AlphaDummy015] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_024 (r : Var) (a : Var) :
    (nb063AlphaDummy016 r a) ∉ (((Class.cv (nb063AlphaDummy009 r a))).fv) := by
  simpa only [nb063AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy009 r a))).fv) 0

theorem nb063_fresh_025 (r : Var) (a : Var) :
    (nb063AlphaDummy017 r a) ∉ (((Class.cv (nb063AlphaDummy009 r a))).fv) := by
  simpa only [nb063AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy009 r a))).fv) 1

theorem nb063_distinct_026 (r : Var) (a : Var) :
    (nb063AlphaDummy016 r a) ≠ (nb063AlphaDummy017 r a) := by
  simpa only [nb063AlphaDummy016, nb063AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy009 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb063_fresh_027 :
    (nb063AlphaDummy020) ∉
      (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) 0

theorem nb063_fresh_028 :
    (nb063AlphaDummy021) ∉
      (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) 1

theorem nb063_fresh_029 :
    (nb063AlphaDummy022) ∉
      (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) 2

theorem nb063_distinct_030 : (nb063AlphaDummy020) ≠ (nb063AlphaDummy021) := by
  simpa only [nb063AlphaDummy020, nb063AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb063_distinct_031 : (nb063AlphaDummy020) ≠ (nb063AlphaDummy022) := by
  simpa only [nb063AlphaDummy020, nb063AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb063_distinct_032 : (nb063AlphaDummy021) ≠ (nb063AlphaDummy022) := by
  simpa only [nb063AlphaDummy021, nb063AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb063_fresh_033 (r : Var) (a : Var) :
    (nb063AlphaDummy023 r a) ∉
      (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 0

theorem nb063_fresh_034 (r : Var) (a : Var) :
    (nb063AlphaDummy024 r a) ∉
      (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 1

theorem nb063_fresh_035 (r : Var) (a : Var) :
    (nb063AlphaDummy025 r a) ∉
      (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 2

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C063C001Part002`. -/


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

theorem nb063_distinct_036 (r : Var) (a : Var) :
    (nb063AlphaDummy023 r a) ≠ (nb063AlphaDummy024 r a) := by
  simpa only [nb063AlphaDummy023, nb063AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb063_distinct_037 (r : Var) (a : Var) :
    (nb063AlphaDummy023 r a) ≠ (nb063AlphaDummy025 r a) := by
  simpa only [nb063AlphaDummy023, nb063AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb063_distinct_038 (r : Var) (a : Var) :
    (nb063AlphaDummy024 r a) ≠ (nb063AlphaDummy025 r a) := by
  simpa only [nb063AlphaDummy024, nb063AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb063_fresh_039 :
    (nb063AlphaDummy032) ∉
      (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy021))).fv) :=
  by
  simpa only [nb063AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy021))).fv)
      0

theorem nb063_fresh_040 :
    (nb063AlphaDummy028) ∉
      (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv) :=
  by
  simpa only [nb063AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv)
      0

theorem nb063_fresh_041 :
    (nb063AlphaDummy034) ∉
      (((Class.cv (nb063AlphaDummy022))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv) :=
  by
  simpa only [nb063AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy022))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv)
      0

theorem nb063_fresh_042 (r : Var) (a : Var) :
    (nb063AlphaDummy033 r a) ∉
      (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy024 r a))).fv) :=
  by
  simpa only [nb063AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy024 r a))).fv)
      0

theorem nb063_fresh_043 (r : Var) (a : Var) :
    (nb063AlphaDummy029 r a) ∉
      (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy025 r a))).fv) :=
  by
  simpa only [nb063AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy025 r a))).fv)
      0

theorem nb063_fresh_044 (r : Var) (a : Var) :
    (nb063AlphaDummy035 r a) ∉
      (((Class.cv (nb063AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy025 r a))).fv) :=
  by
  simpa only [nb063AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy025 r a))).fv)
      0

theorem nb063_fresh_045 :
    (nb063AlphaDummy050) ∉ (((Class.cv (nb063AlphaDummy043))).fv) := by
  simpa only [nb063AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy043))).fv) 0

theorem nb063_fresh_046 :
    (nb063AlphaDummy051) ∉ (((Class.cv (nb063AlphaDummy043))).fv) := by
  simpa only [nb063AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy043))).fv) 1

theorem nb063_distinct_047 : (nb063AlphaDummy050) ≠ (nb063AlphaDummy051) := by
  simpa only [nb063AlphaDummy050, nb063AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy043))).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_048 (x : Var) (y : Var) :
    (nb063AlphaDummy052 x y) ∉ (((Class.cv (nb063AlphaDummy045 x y))).fv) := by
  simpa only [nb063AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy045 x y))).fv) 0

theorem nb063_fresh_049 (x : Var) (y : Var) :
    (nb063AlphaDummy053 x y) ∉ (((Class.cv (nb063AlphaDummy045 x y))).fv) := by
  simpa only [nb063AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy045 x y))).fv) 1

theorem nb063_distinct_050 (x : Var) (y : Var) :
    (nb063AlphaDummy052 x y) ≠ (nb063AlphaDummy053 x y) := by
  simpa only [nb063AlphaDummy052, nb063AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy045 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb063_fresh_051 :
    (nb063AlphaDummy056) ∉
      (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) 0

theorem nb063_fresh_052 :
    (nb063AlphaDummy057) ∉
      (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) 1

theorem nb063_fresh_053 :
    (nb063AlphaDummy058) ∉
      (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) 2

theorem nb063_distinct_054 : (nb063AlphaDummy056) ≠ (nb063AlphaDummy057) := by
  simpa only [nb063AlphaDummy056, nb063AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb063_distinct_055 : (nb063AlphaDummy056) ≠ (nb063AlphaDummy058) := by
  simpa only [nb063AlphaDummy056, nb063AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb063_distinct_056 : (nb063AlphaDummy057) ≠ (nb063AlphaDummy058) := by
  simpa only [nb063AlphaDummy057, nb063AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb063_fresh_057 (x : Var) (y : Var) :
    (nb063AlphaDummy059 x y) ∉
      (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb063_fresh_058 (x : Var) (y : Var) :
    (nb063AlphaDummy060 x y) ∉
      (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb063_fresh_059 (x : Var) (y : Var) :
    (nb063AlphaDummy061 x y) ∉
      (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb063_distinct_060 (x : Var) (y : Var) :
    (nb063AlphaDummy059 x y) ≠ (nb063AlphaDummy060 x y) := by
  simpa only [nb063AlphaDummy059, nb063AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb063_distinct_061 (x : Var) (y : Var) :
    (nb063AlphaDummy059 x y) ≠ (nb063AlphaDummy061 x y) := by
  simpa only [nb063AlphaDummy059, nb063AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb063_distinct_062 (x : Var) (y : Var) :
    (nb063AlphaDummy060 x y) ≠ (nb063AlphaDummy061 x y) := by
  simpa only [nb063AlphaDummy060, nb063AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb063_fresh_063 :
    (nb063AlphaDummy068) ∉
      (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy057))).fv) :=
  by
  simpa only [nb063AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy057))).fv)
      0

theorem nb063_fresh_064 :
    (nb063AlphaDummy064) ∉
      (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv) :=
  by
  simpa only [nb063AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv)
      0

theorem nb063_fresh_065 :
    (nb063AlphaDummy070) ∉
      (((Class.cv (nb063AlphaDummy058))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv) :=
  by
  simpa only [nb063AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy058))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv)
      0

theorem nb063_fresh_066 (x : Var) (y : Var) :
    (nb063AlphaDummy069 x y) ∉
      (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb063AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy060 x y))).fv)
      0

theorem nb063_fresh_067 (x : Var) (y : Var) :
    (nb063AlphaDummy065 x y) ∉
      (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb063AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy061 x y))).fv)
      0

theorem nb063_fresh_068 (x : Var) (y : Var) :
    (nb063AlphaDummy071 x y) ∉
      (((Class.cv (nb063AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb063AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy061 x y))).fv)
      0

theorem nb063_fresh_069 :
    (nb063AlphaDummy086) ∉ (((Class.cv (nb063AlphaDummy079))).fv) := by
  simpa only [nb063AlphaDummy086] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy079))).fv) 0

theorem nb063_fresh_070 :
    (nb063AlphaDummy087) ∉ (((Class.cv (nb063AlphaDummy079))).fv) := by
  simpa only [nb063AlphaDummy087] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy079))).fv) 1

theorem nb063_distinct_071 : (nb063AlphaDummy086) ≠ (nb063AlphaDummy087) := by
  simpa only [nb063AlphaDummy086, nb063AlphaDummy087] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy079))).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_072 (x : Var) (y : Var) :
    (nb063AlphaDummy088 x y) ∉ (((Class.cv (nb063AlphaDummy081 x y))).fv) := by
  simpa only [nb063AlphaDummy088] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy081 x y))).fv) 0

theorem nb063_fresh_073 (x : Var) (y : Var) :
    (nb063AlphaDummy089 x y) ∉ (((Class.cv (nb063AlphaDummy081 x y))).fv) := by
  simpa only [nb063AlphaDummy089] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy081 x y))).fv) 1

theorem nb063_distinct_074 (x : Var) (y : Var) :
    (nb063AlphaDummy088 x y) ≠ (nb063AlphaDummy089 x y) := by
  simpa only [nb063AlphaDummy088, nb063AlphaDummy089] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy081 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb063_fresh_075 :
    (nb063AlphaDummy092) ∉
      (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy092] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) 0

theorem nb063_fresh_076 :
    (nb063AlphaDummy093) ∉
      (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy093] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) 1

theorem nb063_fresh_077 :
    (nb063AlphaDummy094) ∉
      (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy094] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) 2

theorem nb063_distinct_078 : (nb063AlphaDummy092) ≠ (nb063AlphaDummy093) := by
  simpa only [nb063AlphaDummy092, nb063AlphaDummy093] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb063_distinct_079 : (nb063AlphaDummy092) ≠ (nb063AlphaDummy094) := by
  simpa only [nb063AlphaDummy092, nb063AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb063_distinct_080 : (nb063AlphaDummy093) ≠ (nb063AlphaDummy094) := by
  simpa only [nb063AlphaDummy093, nb063AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb063_fresh_081 (x : Var) (y : Var) :
    (nb063AlphaDummy095 x y) ∉
      (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy095] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb063_fresh_082 (x : Var) (y : Var) :
    (nb063AlphaDummy096 x y) ∉
      (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb063_fresh_083 (x : Var) (y : Var) :
    (nb063AlphaDummy097 x y) ∉
      (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb063AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb063_distinct_084 (x : Var) (y : Var) :
    (nb063AlphaDummy095 x y) ≠ (nb063AlphaDummy096 x y) := by
  simpa only [nb063AlphaDummy095, nb063AlphaDummy096] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb063_distinct_085 (x : Var) (y : Var) :
    (nb063AlphaDummy095 x y) ≠ (nb063AlphaDummy097 x y) := by
  simpa only [nb063AlphaDummy095, nb063AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb063_distinct_086 (x : Var) (y : Var) :
    (nb063AlphaDummy096 x y) ≠ (nb063AlphaDummy097 x y) := by
  simpa only [nb063AlphaDummy096, nb063AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb063_fresh_087 :
    (nb063AlphaDummy104) ∉
      (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy093))).fv) :=
  by
  simpa only [nb063AlphaDummy104] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy093))).fv)
      0

theorem nb063_fresh_088 :
    (nb063AlphaDummy100) ∉
      (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv) :=
  by
  simpa only [nb063AlphaDummy100] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv)
      0

theorem nb063_fresh_089 :
    (nb063AlphaDummy106) ∉
      (((Class.cv (nb063AlphaDummy094))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv) :=
  by
  simpa only [nb063AlphaDummy106] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy094))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv)
      0

theorem nb063_fresh_090 (x : Var) (y : Var) :
    (nb063AlphaDummy105 x y) ∉
      (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy096 x y))).fv) :=
  by
  simpa only [nb063AlphaDummy105] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy096 x y))).fv)
      0

theorem nb063_fresh_091 (x : Var) (y : Var) :
    (nb063AlphaDummy101 x y) ∉
      (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy097 x y))).fv) :=
  by
  simpa only [nb063AlphaDummy101] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy097 x y))).fv)
      0

theorem nb063_fresh_092 (x : Var) (y : Var) :
    (nb063AlphaDummy107 x y) ∉
      (((Class.cv (nb063AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy097 x y))).fv) :=
  by
  simpa only [nb063AlphaDummy107] using
    freshVar_not_mem
      (((Class.cv (nb063AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy097 x y))).fv)
      0

theorem nb063_fresh_093 (r : Var) (a : Var) :
    (nb063AlphaDummy008 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb063AlphaDummy008] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb063_fresh_094 (r : Var) (a : Var) :
    (nb063AlphaDummy009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb063AlphaDummy009] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb063_distinct_095 (r : Var) (a : Var) :
    (nb063AlphaDummy008 r a) ≠ (nb063AlphaDummy009 r a) := by
  simpa only [nb063AlphaDummy008, nb063AlphaDummy009] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_096 (x : Var) (y : Var) :
    (nb063AlphaDummy044 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb063AlphaDummy044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb063_fresh_097 (x : Var) (y : Var) :
    (nb063AlphaDummy045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb063AlphaDummy045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb063_distinct_098 (x : Var) (y : Var) :
    (nb063AlphaDummy044 x y) ≠ (nb063AlphaDummy045 x y) := by
  simpa only [nb063AlphaDummy044, nb063AlphaDummy045] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_099 (x : Var) (y : Var) :
    (nb063AlphaDummy080 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb063AlphaDummy080] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0

theorem nb063_fresh_100 (x : Var) (y : Var) :
    (nb063AlphaDummy081 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb063AlphaDummy081] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1

theorem nb063_distinct_101 (x : Var) (y : Var) :
    (nb063AlphaDummy080 x y) ≠ (nb063AlphaDummy081 x y) := by
  simpa only [nb063AlphaDummy080, nb063AlphaDummy081] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_102 :
    (nb063AlphaDummy018) ∉
      (((Wff.classMem (Class.cv (nb063AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy014))).fv) :=
  by
  simpa only [nb063AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb063AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy014))).fv)
      0

theorem nb063_fresh_103 (r : Var) (a : Var) :
    (nb063AlphaDummy019 r a) ∉
      (((Wff.classMem (Class.cv (nb063AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy016 r a))).fv) :=
  by
  simpa only [nb063AlphaDummy019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb063AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy016 r a))).fv)
      0

theorem nb063_fresh_104 :
    (nb063AlphaDummy054) ∉
      (((Wff.classMem (Class.cv (nb063AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy050))).fv) :=
  by
  simpa only [nb063AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb063AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy050))).fv)
      0

theorem nb063_fresh_105 (x : Var) (y : Var) :
    (nb063AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb063AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb063AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb063AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy052 x y))).fv)
      0

theorem nb063_fresh_106 :
    (nb063AlphaDummy090) ∉
      (((Wff.classMem (Class.cv (nb063AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy086))).fv) :=
  by
  simpa only [nb063AlphaDummy090] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb063AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy086))).fv)
      0

theorem nb063_fresh_107 (x : Var) (y : Var) :
    (nb063AlphaDummy091 x y) ∉
      (((Wff.classMem (Class.cv (nb063AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy088 x y))).fv) :=
  by
  simpa only [nb063AlphaDummy091] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb063AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy088 x y))).fv)
      0

theorem nb063_fresh_108 :
    (nb063AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb063AlphaDummy006)
              (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
                (Wff.classEq (Class.cv (nb063AlphaDummy006))
                  (synCphi (Class.cv (nb063AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy006)
              (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
                (Wff.classEq (Class.cv (nb063AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb063AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb063AlphaDummy006)
              (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
                (Wff.classEq (Class.cv (nb063AlphaDummy006))
                  (synCphi (Class.cv (nb063AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy006)
              (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
                (Wff.classEq (Class.cv (nb063AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb063_fresh_109 (r : Var) (a : Var) :
    (nb063AlphaDummy011 r a) ∉
      (((synCcompl (Class.cab (nb063AlphaDummy008 r a)
              (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                  (synCphi (Class.cv (nb063AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy008 r a)
              (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb063AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb063AlphaDummy008 r a)
              (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                  (synCphi (Class.cv (nb063AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy008 r a)
              (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb063_fresh_110 :
    (nb063AlphaDummy046) ∉
      (((synCcompl (Class.cab (nb063AlphaDummy042)
              (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
                (Wff.classEq (Class.cv (nb063AlphaDummy042))
                  (synCphi (Class.cv (nb063AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy042)
              (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
                (Wff.classEq (Class.cv (nb063AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb063AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb063AlphaDummy042)
              (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
                (Wff.classEq (Class.cv (nb063AlphaDummy042))
                  (synCphi (Class.cv (nb063AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy042)
              (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
                (Wff.classEq (Class.cv (nb063AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb063_fresh_111 (x : Var) (y : Var) :
    (nb063AlphaDummy047 x y) ∉
      (((synCcompl (Class.cab (nb063AlphaDummy044 x y)
              (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                  (synCphi (Class.cv (nb063AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy044 x y)
              (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb063AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb063AlphaDummy044 x y)
              (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                  (synCphi (Class.cv (nb063AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy044 x y)
              (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb063_fresh_112 :
    (nb063AlphaDummy082) ∉
      (((synCcompl (Class.cab (nb063AlphaDummy078)
              (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
                (Wff.classEq (Class.cv (nb063AlphaDummy078))
                  (synCphi (Class.cv (nb063AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy078)
              (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
                (Wff.classEq (Class.cv (nb063AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb063AlphaDummy082] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb063AlphaDummy078)
              (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
                (Wff.classEq (Class.cv (nb063AlphaDummy078))
                  (synCphi (Class.cv (nb063AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy078)
              (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
                (Wff.classEq (Class.cv (nb063AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb063_fresh_113 (x : Var) (y : Var) :
    (nb063AlphaDummy083 x y) ∉
      (((synCcompl (Class.cab (nb063AlphaDummy080 x y)
              (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                  (synCphi (Class.cv (nb063AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy080 x y)
              (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb063AlphaDummy083] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb063AlphaDummy080 x y)
              (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                  (synCphi (Class.cv (nb063AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy080 x y)
              (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb063_fresh_114 :
    (nb063AlphaDummy030) ∉
      (((synCcompl (Class.cv (nb063AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy022)))).fv) :=
  by
  simpa only [nb063AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb063AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy022)))).fv)
      0

theorem nb063_fresh_115 (r : Var) (a : Var) :
    (nb063AlphaDummy031 r a) ∉
      (((synCcompl (Class.cv (nb063AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy025 r a)))).fv) :=
  by
  simpa only [nb063AlphaDummy031] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb063AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy025 r a)))).fv)
      0

theorem nb063_fresh_116 :
    (nb063AlphaDummy066) ∉
      (((synCcompl (Class.cv (nb063AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy058)))).fv) :=
  by
  simpa only [nb063AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb063AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy058)))).fv)
      0

theorem nb063_fresh_117 (x : Var) (y : Var) :
    (nb063AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb063AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb063AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb063AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy061 x y)))).fv)
      0

theorem nb063_fresh_118 :
    (nb063AlphaDummy102) ∉
      (((synCcompl (Class.cv (nb063AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy094)))).fv) :=
  by
  simpa only [nb063AlphaDummy102] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb063AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy094)))).fv)
      0

theorem nb063_fresh_119 (x : Var) (y : Var) :
    (nb063AlphaDummy103 x y) ∉
      (((synCcompl (Class.cv (nb063AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy097 x y)))).fv) :=
  by
  simpa only [nb063AlphaDummy103] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb063AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy097 x y)))).fv)
      0

theorem nb063_fresh_120 :
    (nb063AlphaDummy038) ∉
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb063AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb063_fresh_121 (r : Var) (a : Var) :
    (nb063AlphaDummy039 r a) ∉
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb063AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb063_fresh_122 :
    (nb063AlphaDummy074) ∉
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb063AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb063_fresh_123 (x : Var) (y : Var) :
    (nb063AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb063AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb063_fresh_124 :
    (nb063AlphaDummy110) ∉
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb063AlphaDummy110] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb063_fresh_125 (x : Var) (y : Var) :
    (nb063AlphaDummy111 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb063AlphaDummy111] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb063_fresh_126 :
    (nb063AlphaDummy026) ∉
      (((synCnin (Class.cv (nb063AlphaDummy021)) (Class.cv (nb063AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy021))
            (Class.cv (nb063AlphaDummy022)))).fv) :=
  by
  simpa only [nb063AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb063AlphaDummy021)) (Class.cv (nb063AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy021)) (Class.cv (nb063AlphaDummy022)))).fv)
      0

theorem nb063_fresh_127 (r : Var) (a : Var) :
    (nb063AlphaDummy027 r a) ∉
      (((synCnin (Class.cv (nb063AlphaDummy024 r a))
            (Class.cv (nb063AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy024 r a))
            (Class.cv (nb063AlphaDummy025 r a)))).fv) :=
  by
  simpa only [nb063AlphaDummy027] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb063AlphaDummy024 r a))
            (Class.cv (nb063AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy024 r a))
            (Class.cv (nb063AlphaDummy025 r a)))).fv)
      0

theorem nb063_fresh_128 :
    (nb063AlphaDummy062) ∉
      (((synCnin (Class.cv (nb063AlphaDummy057)) (Class.cv (nb063AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy057))
            (Class.cv (nb063AlphaDummy058)))).fv) :=
  by
  simpa only [nb063AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb063AlphaDummy057)) (Class.cv (nb063AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy057)) (Class.cv (nb063AlphaDummy058)))).fv)
      0

theorem nb063_fresh_129 (x : Var) (y : Var) :
    (nb063AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb063AlphaDummy060 x y))
            (Class.cv (nb063AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy060 x y))
            (Class.cv (nb063AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb063AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb063AlphaDummy060 x y))
            (Class.cv (nb063AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy060 x y))
            (Class.cv (nb063AlphaDummy061 x y)))).fv)
      0

theorem nb063_fresh_130 :
    (nb063AlphaDummy098) ∉
      (((synCnin (Class.cv (nb063AlphaDummy093)) (Class.cv (nb063AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy093))
            (Class.cv (nb063AlphaDummy094)))).fv) :=
  by
  simpa only [nb063AlphaDummy098] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb063AlphaDummy093)) (Class.cv (nb063AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy093)) (Class.cv (nb063AlphaDummy094)))).fv)
      0

theorem nb063_fresh_131 (x : Var) (y : Var) :
    (nb063AlphaDummy099 x y) ∉
      (((synCnin (Class.cv (nb063AlphaDummy096 x y))
            (Class.cv (nb063AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy096 x y))
            (Class.cv (nb063AlphaDummy097 x y)))).fv) :=
  by
  simpa only [nb063AlphaDummy099] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb063AlphaDummy096 x y))
            (Class.cv (nb063AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy096 x y))
            (Class.cv (nb063AlphaDummy097 x y)))).fv)
      0

theorem nb063_fresh_132 :
    (nb063AlphaDummy040) ∉
      (((synCphi (Class.cv (nb063AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy007)))).fv) :=
  by
  simpa only [nb063AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb063AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy007)))).fv)
      0

theorem nb063_fresh_133 (r : Var) (a : Var) :
    (nb063AlphaDummy041 r a) ∉
      (((synCphi (Class.cv (nb063AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy009 r a)))).fv) :=
  by
  simpa only [nb063AlphaDummy041] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb063AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy009 r a)))).fv)
      0

theorem nb063_fresh_134 :
    (nb063AlphaDummy076) ∉
      (((synCphi (Class.cv (nb063AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy043)))).fv) :=
  by
  simpa only [nb063AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb063AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy043)))).fv)
      0

theorem nb063_fresh_135 (x : Var) (y : Var) :
    (nb063AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb063AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy045 x y)))).fv) :=
  by
  simpa only [nb063AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb063AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy045 x y)))).fv)
      0

theorem nb063_fresh_136 :
    (nb063AlphaDummy112) ∉
      (((synCphi (Class.cv (nb063AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy079)))).fv) :=
  by
  simpa only [nb063AlphaDummy112] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb063AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy079)))).fv)
      0

theorem nb063_fresh_137 (x : Var) (y : Var) :
    (nb063AlphaDummy113 x y) ∉
      (((synCphi (Class.cv (nb063AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy081 x y)))).fv) :=
  by
  simpa only [nb063AlphaDummy113] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb063AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy081 x y)))).fv)
      0

theorem nb063_fresh_138 :
    (nb063AlphaDummy004) ∉
      (({(nb063AlphaDummy001)} : Finset Var) ∪ ({(nb063AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb063AlphaDummy002) (Class.cv (nb063AlphaDummy000))
            (synWral (nb063AlphaDummy003) (Class.cv (nb063AlphaDummy000)) (synWo
                (synWbr (Class.cv (nb063AlphaDummy002))
                  (Class.cv (nb063AlphaDummy001)) (Class.cv (nb063AlphaDummy003)))
                (synWbr (Class.cv (nb063AlphaDummy003)) (Class.cv (nb063AlphaDummy001))
                  (Class.cv (nb063AlphaDummy002))))))).fv) :=
  by
  simpa only [nb063AlphaDummy004] using
    freshVar_not_mem
      (({(nb063AlphaDummy001)} : Finset Var) ∪ ({(nb063AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb063AlphaDummy002) (Class.cv (nb063AlphaDummy000))
            (synWral (nb063AlphaDummy003) (Class.cv (nb063AlphaDummy000)) (synWo
                (synWbr (Class.cv (nb063AlphaDummy002))
                  (Class.cv (nb063AlphaDummy001)) (Class.cv (nb063AlphaDummy003)))
                (synWbr (Class.cv (nb063AlphaDummy003)) (Class.cv (nb063AlphaDummy001))
                  (Class.cv (nb063AlphaDummy002))))))).fv)
      0

theorem nb063_fresh_139 (x : Var) (y : Var) (r : Var) (a : Var) :
    (nb063AlphaDummy005 x y r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (synWo (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) :=
  by
  simpa only [nb063AlphaDummy005] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (synWo (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv)
      0

theorem nb063_fresh_140 : (nb063AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb063AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb063_fresh_141 : (nb063AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb063AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb063_fresh_142 : (nb063AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb063AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb063_fresh_143 : (nb063AlphaDummy003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb063AlphaDummy003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb063_distinct_144 : (nb063AlphaDummy000) ≠ (nb063AlphaDummy001) := by
  simpa only [nb063AlphaDummy000, nb063AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb063_distinct_145 : (nb063AlphaDummy000) ≠ (nb063AlphaDummy002) := by
  simpa only [nb063AlphaDummy000, nb063AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb063_distinct_146 : (nb063AlphaDummy000) ≠ (nb063AlphaDummy003) := by
  simpa only [nb063AlphaDummy000, nb063AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb063_distinct_147 : (nb063AlphaDummy001) ≠ (nb063AlphaDummy002) := by
  simpa only [nb063AlphaDummy001, nb063AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb063_distinct_148 : (nb063AlphaDummy001) ≠ (nb063AlphaDummy003) := by
  simpa only [nb063AlphaDummy001, nb063AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb063_distinct_149 : (nb063AlphaDummy002) ≠ (nb063AlphaDummy003) := by
  simpa only [nb063AlphaDummy002, nb063AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb063_support_mem_0000 :
    (nb063AlphaDummy001) ∈
      (({(nb063AlphaDummy001)} : Finset Var) ∪ ({(nb063AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb063AlphaDummy002) (Class.cv (nb063AlphaDummy000))
            (synWral (nb063AlphaDummy003) (Class.cv (nb063AlphaDummy000)) (synWo
                (synWbr (Class.cv (nb063AlphaDummy002))
                  (Class.cv (nb063AlphaDummy001)) (Class.cv (nb063AlphaDummy003)))
                (synWbr (Class.cv (nb063AlphaDummy003)) (Class.cv (nb063AlphaDummy001))
                  (Class.cv (nb063AlphaDummy002))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0001 (x : Var) (y : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (synWo (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0002 :
    (nb063AlphaDummy000) ∈
      (({(nb063AlphaDummy001)} : Finset Var) ∪ ({(nb063AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb063AlphaDummy002) (Class.cv (nb063AlphaDummy000))
            (synWral (nb063AlphaDummy003) (Class.cv (nb063AlphaDummy000)) (synWo
                (synWbr (Class.cv (nb063AlphaDummy002))
                  (Class.cv (nb063AlphaDummy001)) (Class.cv (nb063AlphaDummy003)))
                (synWbr (Class.cv (nb063AlphaDummy003)) (Class.cv (nb063AlphaDummy001))
                  (Class.cv (nb063AlphaDummy002))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0003 (x : Var) (y : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (synWo (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0004 :
    (nb063AlphaDummy001) ∈
      (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0005 :
    (nb063AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb063AlphaDummy006)
              (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
                (Wff.classEq (Class.cv (nb063AlphaDummy006))
                  (synCphi (Class.cv (nb063AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy006)
              (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
                (Wff.classEq (Class.cv (nb063AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((synCcompl (Class.cab (nb063AlphaDummy008 r a)
              (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                  (synCphi (Class.cv (nb063AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy008 r a)
              (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0008 :
    (nb063AlphaDummy001) ∈
      (((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCphi (Class.cv (nb063AlphaDummy007))))))).fv ∪
        ((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCphi (Class.cv (nb063AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCphi (Class.cv (nb063AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCphi (Class.cv (nb063AlphaDummy009 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0010 :
    (nb063AlphaDummy007) ∈ (((Class.cv (nb063AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0011 (r : Var) (a : Var) :
    (nb063AlphaDummy009 r a) ∈ (((Class.cv (nb063AlphaDummy009 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0012 :
    (nb063AlphaDummy014) ∈
      (((Wff.classMem (Class.cv (nb063AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy014))).fv) :=
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

theorem nb063_support_mem_0013 (r : Var) (a : Var) :
    (nb063AlphaDummy016 r a) ∈
      (((Wff.classMem (Class.cv (nb063AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy016 r a))).fv) :=
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

theorem nb063_support_mem_0014 :
    (nb063AlphaDummy014) ∈
      (((Class.cv (nb063AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0015 (r : Var) (a : Var) :
    (nb063AlphaDummy016 r a) ∈
      (((Class.cv (nb063AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0016 :
    (nb063AlphaDummy021) ∈
      (((synCnin (Class.cv (nb063AlphaDummy021)) (Class.cv (nb063AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy021))
            (Class.cv (nb063AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0017 (r : Var) (a : Var) :
    (nb063AlphaDummy024 r a) ∈
      (((synCnin (Class.cv (nb063AlphaDummy024 r a))
            (Class.cv (nb063AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy024 r a))
            (Class.cv (nb063AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0018 :
    (nb063AlphaDummy021) ∈
      (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0019 (r : Var) (a : Var) :
    (nb063AlphaDummy024 r a) ∈
      (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0020 :
    (nb063AlphaDummy022) ∈
      (((synCnin (Class.cv (nb063AlphaDummy021)) (Class.cv (nb063AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy021))
            (Class.cv (nb063AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0021 (r : Var) (a : Var) :
    (nb063AlphaDummy025 r a) ∈
      (((synCnin (Class.cv (nb063AlphaDummy024 r a))
            (Class.cv (nb063AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy024 r a))
            (Class.cv (nb063AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0022 :
    (nb063AlphaDummy022) ∈
      (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0023 (r : Var) (a : Var) :
    (nb063AlphaDummy025 r a) ∈
      (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0024 :
    (nb063AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0025 (r : Var) (a : Var) :
    (nb063AlphaDummy024 r a) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0026 :
    (nb063AlphaDummy021) ∈
      (((Class.cv (nb063AlphaDummy021))).fv ∪ ((Class.cv (nb063AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0027 (r : Var) (a : Var) :
    (nb063AlphaDummy024 r a) ∈
      (((Class.cv (nb063AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0028 :
    (nb063AlphaDummy022) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0029 (r : Var) (a : Var) :
    (nb063AlphaDummy025 r a) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0030 :
    (nb063AlphaDummy022) ∈
      (((Class.cv (nb063AlphaDummy022))).fv ∪ ((Class.cv (nb063AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0031 (r : Var) (a : Var) :
    (nb063AlphaDummy025 r a) ∈
      (((Class.cv (nb063AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb063AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0032 :
    (nb063AlphaDummy000) ∈
      (((Class.cv (nb063AlphaDummy001))).fv ∪ ((Class.cv (nb063AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0033 :
    (nb063AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb063AlphaDummy006)
              (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy001))
                (Wff.classEq (Class.cv (nb063AlphaDummy006))
                  (synCphi (Class.cv (nb063AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy006)
              (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
                (Wff.classEq (Class.cv (nb063AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((synCcompl (Class.cab (nb063AlphaDummy008 r a)
              (synWrex (nb063AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                  (synCphi (Class.cv (nb063AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy008 r a)
              (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C063C001Part003`. -/


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

theorem nb063_support_mem_0036 :
    (nb063AlphaDummy000) ∈
      (((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy006)
            (synWrex (nb063AlphaDummy007) (Class.cv (nb063AlphaDummy000))
              (Wff.classEq (Class.cv (nb063AlphaDummy006))
                (synCun (synCphi (Class.cv (nb063AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy008 r a)
            (synWrex (nb063AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb063AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb063AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0038 :
    (nb063AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0039 (r : Var) (a : Var) :
    (nb063AlphaDummy009 r a) ∈
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0040 :
    (nb063AlphaDummy007) ∈
      (((synCphi (Class.cv (nb063AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0041 (r : Var) (a : Var) :
    (nb063AlphaDummy009 r a) ∈
      (((synCphi (Class.cv (nb063AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy009 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0042 :
    (nb063AlphaDummy002) ∈
      (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0043 :
    (nb063AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb063AlphaDummy042)
              (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
                (Wff.classEq (Class.cv (nb063AlphaDummy042))
                  (synCphi (Class.cv (nb063AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy042)
              (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
                (Wff.classEq (Class.cv (nb063AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0044 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0045 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb063AlphaDummy044 x y)
              (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                  (synCphi (Class.cv (nb063AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy044 x y)
              (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0046 :
    (nb063AlphaDummy002) ∈
      (((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCphi (Class.cv (nb063AlphaDummy043))))))).fv ∪
        ((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCphi (Class.cv (nb063AlphaDummy043))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0047 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCphi (Class.cv (nb063AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCphi (Class.cv (nb063AlphaDummy045 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0048 :
    (nb063AlphaDummy043) ∈ (((Class.cv (nb063AlphaDummy043))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0049 (x : Var) (y : Var) :
    (nb063AlphaDummy045 x y) ∈ (((Class.cv (nb063AlphaDummy045 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0050 :
    (nb063AlphaDummy050) ∈
      (((Wff.classMem (Class.cv (nb063AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy050))).fv) :=
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

theorem nb063_support_mem_0051 (x : Var) (y : Var) :
    (nb063AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb063AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy052 x y))).fv) :=
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

theorem nb063_support_mem_0052 :
    (nb063AlphaDummy050) ∈
      (((Class.cv (nb063AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0053 (x : Var) (y : Var) :
    (nb063AlphaDummy052 x y) ∈
      (((Class.cv (nb063AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0054 :
    (nb063AlphaDummy057) ∈
      (((synCnin (Class.cv (nb063AlphaDummy057)) (Class.cv (nb063AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy057))
            (Class.cv (nb063AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0055 (x : Var) (y : Var) :
    (nb063AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb063AlphaDummy060 x y))
            (Class.cv (nb063AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy060 x y))
            (Class.cv (nb063AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0056 :
    (nb063AlphaDummy057) ∈
      (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0057 (x : Var) (y : Var) :
    (nb063AlphaDummy060 x y) ∈
      (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0058 :
    (nb063AlphaDummy058) ∈
      (((synCnin (Class.cv (nb063AlphaDummy057)) (Class.cv (nb063AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy057))
            (Class.cv (nb063AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0059 (x : Var) (y : Var) :
    (nb063AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb063AlphaDummy060 x y))
            (Class.cv (nb063AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy060 x y))
            (Class.cv (nb063AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0060 :
    (nb063AlphaDummy058) ∈
      (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0061 (x : Var) (y : Var) :
    (nb063AlphaDummy061 x y) ∈
      (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0062 :
    (nb063AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0063 (x : Var) (y : Var) :
    (nb063AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0064 :
    (nb063AlphaDummy057) ∈
      (((Class.cv (nb063AlphaDummy057))).fv ∪ ((Class.cv (nb063AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0065 (x : Var) (y : Var) :
    (nb063AlphaDummy060 x y) ∈
      (((Class.cv (nb063AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0066 :
    (nb063AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0067 (x : Var) (y : Var) :
    (nb063AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0068 :
    (nb063AlphaDummy058) ∈
      (((Class.cv (nb063AlphaDummy058))).fv ∪ ((Class.cv (nb063AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0069 (x : Var) (y : Var) :
    (nb063AlphaDummy061 x y) ∈
      (((Class.cv (nb063AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0070 :
    (nb063AlphaDummy003) ∈
      (((Class.cv (nb063AlphaDummy002))).fv ∪ ((Class.cv (nb063AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0071 :
    (nb063AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb063AlphaDummy042)
              (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy002))
                (Wff.classEq (Class.cv (nb063AlphaDummy042))
                  (synCphi (Class.cv (nb063AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy042)
              (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
                (Wff.classEq (Class.cv (nb063AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0072 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0073 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb063AlphaDummy044 x y)
              (synWrex (nb063AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                  (synCphi (Class.cv (nb063AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy044 x y)
              (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0074 :
    (nb063AlphaDummy003) ∈
      (((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy042)
            (synWrex (nb063AlphaDummy043) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy042))
                (synCun (synCphi (Class.cv (nb063AlphaDummy043)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0075 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy044 x y)
            (synWrex (nb063AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0076 :
    (nb063AlphaDummy043) ∈
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0077 (x : Var) (y : Var) :
    (nb063AlphaDummy045 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0078 :
    (nb063AlphaDummy043) ∈
      (((synCphi (Class.cv (nb063AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy043)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0079 (x : Var) (y : Var) :
    (nb063AlphaDummy045 x y) ∈
      (((synCphi (Class.cv (nb063AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy045 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0080 :
    (nb063AlphaDummy003) ∈
      (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0081 :
    (nb063AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb063AlphaDummy078)
              (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
                (Wff.classEq (Class.cv (nb063AlphaDummy078))
                  (synCphi (Class.cv (nb063AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy078)
              (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
                (Wff.classEq (Class.cv (nb063AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0082 (x : Var) (y : Var) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0083 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb063AlphaDummy080 x y)
              (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                  (synCphi (Class.cv (nb063AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy080 x y)
              (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0084 :
    (nb063AlphaDummy003) ∈
      (((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCphi (Class.cv (nb063AlphaDummy079))))))).fv ∪
        ((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCphi (Class.cv (nb063AlphaDummy079))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0085 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCphi (Class.cv (nb063AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCphi (Class.cv (nb063AlphaDummy081 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0086 :
    (nb063AlphaDummy079) ∈ (((Class.cv (nb063AlphaDummy079))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0087 (x : Var) (y : Var) :
    (nb063AlphaDummy081 x y) ∈ (((Class.cv (nb063AlphaDummy081 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0088 :
    (nb063AlphaDummy086) ∈
      (((Wff.classMem (Class.cv (nb063AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy086))).fv) :=
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

theorem nb063_support_mem_0089 (x : Var) (y : Var) :
    (nb063AlphaDummy088 x y) ∈
      (((Wff.classMem (Class.cv (nb063AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb063AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb063AlphaDummy088 x y))).fv) :=
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

theorem nb063_support_mem_0090 :
    (nb063AlphaDummy086) ∈
      (((Class.cv (nb063AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0091 (x : Var) (y : Var) :
    (nb063AlphaDummy088 x y) ∈
      (((Class.cv (nb063AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0092 :
    (nb063AlphaDummy093) ∈
      (((synCnin (Class.cv (nb063AlphaDummy093)) (Class.cv (nb063AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy093))
            (Class.cv (nb063AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0093 (x : Var) (y : Var) :
    (nb063AlphaDummy096 x y) ∈
      (((synCnin (Class.cv (nb063AlphaDummy096 x y))
            (Class.cv (nb063AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy096 x y))
            (Class.cv (nb063AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0094 :
    (nb063AlphaDummy093) ∈
      (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0095 (x : Var) (y : Var) :
    (nb063AlphaDummy096 x y) ∈
      (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0096 :
    (nb063AlphaDummy094) ∈
      (((synCnin (Class.cv (nb063AlphaDummy093)) (Class.cv (nb063AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy093))
            (Class.cv (nb063AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0097 (x : Var) (y : Var) :
    (nb063AlphaDummy097 x y) ∈
      (((synCnin (Class.cv (nb063AlphaDummy096 x y))
            (Class.cv (nb063AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb063AlphaDummy096 x y))
            (Class.cv (nb063AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0098 :
    (nb063AlphaDummy094) ∈
      (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0099 (x : Var) (y : Var) :
    (nb063AlphaDummy097 x y) ∈
      (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0100 :
    (nb063AlphaDummy093) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0101 (x : Var) (y : Var) :
    (nb063AlphaDummy096 x y) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0102 :
    (nb063AlphaDummy093) ∈
      (((Class.cv (nb063AlphaDummy093))).fv ∪ ((Class.cv (nb063AlphaDummy093))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0103 (x : Var) (y : Var) :
    (nb063AlphaDummy096 x y) ∈
      (((Class.cv (nb063AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy096 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0104 :
    (nb063AlphaDummy094) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0105 (x : Var) (y : Var) :
    (nb063AlphaDummy097 x y) ∈
      (((synCcompl (Class.cv (nb063AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb063AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0106 :
    (nb063AlphaDummy094) ∈
      (((Class.cv (nb063AlphaDummy094))).fv ∪ ((Class.cv (nb063AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0107 (x : Var) (y : Var) :
    (nb063AlphaDummy097 x y) ∈
      (((Class.cv (nb063AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb063AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0108 :
    (nb063AlphaDummy002) ∈
      (((Class.cv (nb063AlphaDummy003))).fv ∪ ((Class.cv (nb063AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0109 :
    (nb063AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb063AlphaDummy078)
              (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy003))
                (Wff.classEq (Class.cv (nb063AlphaDummy078))
                  (synCphi (Class.cv (nb063AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy078)
              (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
                (Wff.classEq (Class.cv (nb063AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0110 (x : Var) (y : Var) :
    x ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0111 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb063AlphaDummy080 x y)
              (synWrex (nb063AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                  (synCphi (Class.cv (nb063AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb063AlphaDummy080 x y)
              (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0112 :
    (nb063AlphaDummy002) ∈
      (((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy078)
            (synWrex (nb063AlphaDummy079) (Class.cv (nb063AlphaDummy002))
              (Wff.classEq (Class.cv (nb063AlphaDummy078))
                (synCun (synCphi (Class.cv (nb063AlphaDummy079)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0113 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb063AlphaDummy080 x y)
            (synWrex (nb063AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb063AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0114 :
    (nb063AlphaDummy079) ∈
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0115 (x : Var) (y : Var) :
    (nb063AlphaDummy081 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb063AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0116 :
    (nb063AlphaDummy079) ∈
      (((synCphi (Class.cv (nb063AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy079)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0117 (x : Var) (y : Var) :
    (nb063AlphaDummy081 x y) ∈
      (((synCphi (Class.cv (nb063AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb063AlphaDummy081 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
