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

/-! Certificates from `NAR4C065C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_000`. -/
@[expose]
noncomputable def nb065AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_001`. -/
@[expose]
noncomputable def nb065AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_002`. -/
@[expose]
noncomputable def nb065AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_003`. -/
@[expose]
noncomputable def nb065AlphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_004`. -/
@[expose]
noncomputable def nb065AlphaDummy004 : Var :=
  (freshVar
    (({(nb065AlphaDummy001)} : Finset Var) ∪ ({(nb065AlphaDummy000)} : Finset Var) ∪
      ((synWral (nb065AlphaDummy002) (Class.cv (nb065AlphaDummy000))
          (synWral (nb065AlphaDummy003) (Class.cv (nb065AlphaDummy000)) (Wff.imp
              (synWbr (Class.cv (nb065AlphaDummy002))
                (Class.cv (nb065AlphaDummy001)) (Class.cv (nb065AlphaDummy003)))
              (synWbr (Class.cv (nb065AlphaDummy003)) (Class.cv (nb065AlphaDummy001))
                (Class.cv (nb065AlphaDummy002))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_005`. -/
@[expose]
noncomputable def nb065AlphaDummy005 (x : Var) (y : Var) (r : Var) (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
          (synWral y (Class.cv a) (Wff.imp (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
              (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_006`. -/
@[expose]
noncomputable def nb065AlphaDummy006 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_007`. -/
@[expose]
noncomputable def nb065AlphaDummy007 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_008`. -/
@[expose]
noncomputable def nb065AlphaDummy008 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_009`. -/
@[expose]
noncomputable def nb065AlphaDummy009 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_010`. -/
@[expose]
noncomputable def nb065AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCphi (Class.cv (nb065AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_011`. -/
@[expose]
noncomputable def nb065AlphaDummy011 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCphi (Class.cv (nb065AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
          (Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_012`. -/
@[expose]
noncomputable def nb065AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy006)
          (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
            (Wff.classEq (Class.cv (nb065AlphaDummy006))
              (synCphi (Class.cv (nb065AlphaDummy007))))))).fv ∪
      ((Class.cab (nb065AlphaDummy006)
          (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
            (Wff.classEq (Class.cv (nb065AlphaDummy006))
              (synCphi (Class.cv (nb065AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_013`. -/
@[expose]
noncomputable def nb065AlphaDummy013 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy008 r a)
          (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
              (synCphi (Class.cv (nb065AlphaDummy009 r a))))))).fv ∪
      ((Class.cab (nb065AlphaDummy008 r a) (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
              (synCphi (Class.cv (nb065AlphaDummy009 r a))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_014`. -/
@[expose]
noncomputable def nb065AlphaDummy014 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_015`. -/
@[expose]
noncomputable def nb065AlphaDummy015 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_016`. -/
@[expose]
noncomputable def nb065AlphaDummy016 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy009 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_017`. -/
@[expose]
noncomputable def nb065AlphaDummy017 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy009 r a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_018`. -/
@[expose]
noncomputable def nb065AlphaDummy018 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb065AlphaDummy014)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb065AlphaDummy014)) (synC1c))).fv ∪
      ((Class.cv (nb065AlphaDummy014))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_019`. -/
@[expose]
noncomputable def nb065AlphaDummy019 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb065AlphaDummy016 r a)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb065AlphaDummy016 r a)) (synC1c))).fv ∪
      ((Class.cv (nb065AlphaDummy016 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_020`. -/
@[expose]
noncomputable def nb065AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_021`. -/
@[expose]
noncomputable def nb065AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_022`. -/
@[expose]
noncomputable def nb065AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_023`. -/
@[expose]
noncomputable def nb065AlphaDummy023 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_024`. -/
@[expose]
noncomputable def nb065AlphaDummy024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_025`. -/
@[expose]
noncomputable def nb065AlphaDummy025 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_026`. -/
@[expose]
noncomputable def nb065AlphaDummy026 : Var :=
  (freshVar (((synCnin (Class.cv (nb065AlphaDummy021))
          (Class.cv (nb065AlphaDummy022)))).fv ∪
      ((synCnin (Class.cv (nb065AlphaDummy021)) (Class.cv (nb065AlphaDummy022)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_027`. -/
@[expose]
noncomputable def nb065AlphaDummy027 (r : Var) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb065AlphaDummy024 r a))
          (Class.cv (nb065AlphaDummy025 r a)))).fv ∪
      ((synCnin (Class.cv (nb065AlphaDummy024 r a))
          (Class.cv (nb065AlphaDummy025 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_028`. -/
@[expose]
noncomputable def nb065AlphaDummy028 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_029`. -/
@[expose]
noncomputable def nb065AlphaDummy029 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
      ((Class.cv (nb065AlphaDummy025 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_030`. -/
@[expose]
noncomputable def nb065AlphaDummy030 : Var :=
  (freshVar (((synCcompl (Class.cv (nb065AlphaDummy021)))).fv ∪
      ((synCcompl (Class.cv (nb065AlphaDummy022)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_031`. -/
@[expose]
noncomputable def nb065AlphaDummy031 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb065AlphaDummy024 r a)))).fv ∪
      ((synCcompl (Class.cv (nb065AlphaDummy025 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_032`. -/
@[expose]
noncomputable def nb065AlphaDummy032 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy021))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_033`. -/
@[expose]
noncomputable def nb065AlphaDummy033 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
      ((Class.cv (nb065AlphaDummy024 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_034`. -/
@[expose]
noncomputable def nb065AlphaDummy034 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy022))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_035`. -/
@[expose]
noncomputable def nb065AlphaDummy035 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy025 r a))).fv ∪
      ((Class.cv (nb065AlphaDummy025 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_036`. -/
@[expose]
noncomputable def nb065AlphaDummy036 : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy006)
          (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
            (Wff.classEq (Class.cv (nb065AlphaDummy006))
              (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy006)
          (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
            (Wff.classEq (Class.cv (nb065AlphaDummy006))
              (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_037`. -/
@[expose]
noncomputable def nb065AlphaDummy037 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy008 r a)
          (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
              (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy008 r a)
          (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
              (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_038`. -/
@[expose]
noncomputable def nb065AlphaDummy038 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb065AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_039`. -/
@[expose]
noncomputable def nb065AlphaDummy039 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb065AlphaDummy009 r a))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_040`. -/
@[expose]
noncomputable def nb065AlphaDummy040 : Var :=
  (freshVar (((synCphi (Class.cv (nb065AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb065AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_041`. -/
@[expose]
noncomputable def nb065AlphaDummy041 (r : Var) (a : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb065AlphaDummy009 r a)))).fv ∪
      ((synCphi (Class.cv (nb065AlphaDummy009 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_042`. -/
@[expose]
noncomputable def nb065AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_043`. -/
@[expose]
noncomputable def nb065AlphaDummy043 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_044`. -/
@[expose]
noncomputable def nb065AlphaDummy044 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_045`. -/
@[expose]
noncomputable def nb065AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_046`. -/
@[expose]
noncomputable def nb065AlphaDummy046 : Var :=
  (freshVar (((synCcompl (Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCphi (Class.cv (nb065AlphaDummy043)))))))).fv ∪ ((synCcompl
          (Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_047`. -/
@[expose]
noncomputable def nb065AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCphi (Class.cv (nb065AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_048`. -/
@[expose]
noncomputable def nb065AlphaDummy048 : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy042)
          (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
            (Wff.classEq (Class.cv (nb065AlphaDummy042))
              (synCphi (Class.cv (nb065AlphaDummy043))))))).fv ∪
      ((Class.cab (nb065AlphaDummy042)
          (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
            (Wff.classEq (Class.cv (nb065AlphaDummy042))
              (synCphi (Class.cv (nb065AlphaDummy043))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_049`. -/
@[expose]
noncomputable def nb065AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy044 x y)
          (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
              (synCphi (Class.cv (nb065AlphaDummy045 x y))))))).fv ∪
      ((Class.cab (nb065AlphaDummy044 x y) (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
              (synCphi (Class.cv (nb065AlphaDummy045 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_050`. -/
@[expose]
noncomputable def nb065AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy043))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_051`. -/
@[expose]
noncomputable def nb065AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy043))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_052`. -/
@[expose]
noncomputable def nb065AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy045 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_053`. -/
@[expose]
noncomputable def nb065AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy045 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_054`. -/
@[expose]
noncomputable def nb065AlphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb065AlphaDummy050)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb065AlphaDummy050)) (synC1c))).fv ∪
      ((Class.cv (nb065AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_055`. -/
@[expose]
noncomputable def nb065AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb065AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb065AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb065AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_056`. -/
@[expose]
noncomputable def nb065AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_057`. -/
@[expose]
noncomputable def nb065AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_058`. -/
@[expose]
noncomputable def nb065AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_059`. -/
@[expose]
noncomputable def nb065AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_060`. -/
@[expose]
noncomputable def nb065AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_061`. -/
@[expose]
noncomputable def nb065AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_062`. -/
@[expose]
noncomputable def nb065AlphaDummy062 : Var :=
  (freshVar (((synCnin (Class.cv (nb065AlphaDummy057))
          (Class.cv (nb065AlphaDummy058)))).fv ∪
      ((synCnin (Class.cv (nb065AlphaDummy057)) (Class.cv (nb065AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_063`. -/
@[expose]
noncomputable def nb065AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb065AlphaDummy060 x y))
          (Class.cv (nb065AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb065AlphaDummy060 x y))
          (Class.cv (nb065AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_064`. -/
@[expose]
noncomputable def nb065AlphaDummy064 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_065`. -/
@[expose]
noncomputable def nb065AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb065AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_066`. -/
@[expose]
noncomputable def nb065AlphaDummy066 : Var :=
  (freshVar (((synCcompl (Class.cv (nb065AlphaDummy057)))).fv ∪
      ((synCcompl (Class.cv (nb065AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_067`. -/
@[expose]
noncomputable def nb065AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb065AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb065AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_068`. -/
@[expose]
noncomputable def nb065AlphaDummy068 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_069`. -/
@[expose]
noncomputable def nb065AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb065AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_070`. -/
@[expose]
noncomputable def nb065AlphaDummy070 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy058))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_071`. -/
@[expose]
noncomputable def nb065AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb065AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_072`. -/
@[expose]
noncomputable def nb065AlphaDummy072 : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy042)
          (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
            (Wff.classEq (Class.cv (nb065AlphaDummy042))
              (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy042)
          (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
            (Wff.classEq (Class.cv (nb065AlphaDummy042))
              (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_073`. -/
@[expose]
noncomputable def nb065AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy044 x y)
          (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
              (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy044 x y)
          (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
              (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_074`. -/
@[expose]
noncomputable def nb065AlphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb065AlphaDummy043))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_075`. -/
@[expose]
noncomputable def nb065AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb065AlphaDummy045 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_076`. -/
@[expose]
noncomputable def nb065AlphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv (nb065AlphaDummy043)))).fv ∪
      ((synCphi (Class.cv (nb065AlphaDummy043)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_077`. -/
@[expose]
noncomputable def nb065AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb065AlphaDummy045 x y)))).fv ∪
      ((synCphi (Class.cv (nb065AlphaDummy045 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_078`. -/
@[expose]
noncomputable def nb065AlphaDummy078 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_079`. -/
@[expose]
noncomputable def nb065AlphaDummy079 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_080`. -/
@[expose]
noncomputable def nb065AlphaDummy080 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_081`. -/
@[expose]
noncomputable def nb065AlphaDummy081 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_082`. -/
@[expose]
noncomputable def nb065AlphaDummy082 : Var :=
  (freshVar (((synCcompl (Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCphi (Class.cv (nb065AlphaDummy079)))))))).fv ∪ ((synCcompl
          (Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_083`. -/
@[expose]
noncomputable def nb065AlphaDummy083 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCphi (Class.cv (nb065AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_084`. -/
@[expose]
noncomputable def nb065AlphaDummy084 : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy078)
          (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
            (Wff.classEq (Class.cv (nb065AlphaDummy078))
              (synCphi (Class.cv (nb065AlphaDummy079))))))).fv ∪
      ((Class.cab (nb065AlphaDummy078)
          (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
            (Wff.classEq (Class.cv (nb065AlphaDummy078))
              (synCphi (Class.cv (nb065AlphaDummy079))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_085`. -/
@[expose]
noncomputable def nb065AlphaDummy085 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy080 x y)
          (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
              (synCphi (Class.cv (nb065AlphaDummy081 x y))))))).fv ∪
      ((Class.cab (nb065AlphaDummy080 x y) (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
              (synCphi (Class.cv (nb065AlphaDummy081 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_086`. -/
@[expose]
noncomputable def nb065AlphaDummy086 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy079))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_087`. -/
@[expose]
noncomputable def nb065AlphaDummy087 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy079))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_088`. -/
@[expose]
noncomputable def nb065AlphaDummy088 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy081 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_089`. -/
@[expose]
noncomputable def nb065AlphaDummy089 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy081 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_090`. -/
@[expose]
noncomputable def nb065AlphaDummy090 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb065AlphaDummy086)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb065AlphaDummy086)) (synC1c))).fv ∪
      ((Class.cv (nb065AlphaDummy086))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_091`. -/
@[expose]
noncomputable def nb065AlphaDummy091 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb065AlphaDummy088 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb065AlphaDummy088 x y)) (synC1c))).fv ∪
      ((Class.cv (nb065AlphaDummy088 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_092`. -/
@[expose]
noncomputable def nb065AlphaDummy092 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_093`. -/
@[expose]
noncomputable def nb065AlphaDummy093 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_094`. -/
@[expose]
noncomputable def nb065AlphaDummy094 : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_095`. -/
@[expose]
noncomputable def nb065AlphaDummy095 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_096`. -/
@[expose]
noncomputable def nb065AlphaDummy096 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_097`. -/
@[expose]
noncomputable def nb065AlphaDummy097 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_098`. -/
@[expose]
noncomputable def nb065AlphaDummy098 : Var :=
  (freshVar (((synCnin (Class.cv (nb065AlphaDummy093))
          (Class.cv (nb065AlphaDummy094)))).fv ∪
      ((synCnin (Class.cv (nb065AlphaDummy093)) (Class.cv (nb065AlphaDummy094)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_099`. -/
@[expose]
noncomputable def nb065AlphaDummy099 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb065AlphaDummy096 x y))
          (Class.cv (nb065AlphaDummy097 x y)))).fv ∪
      ((synCnin (Class.cv (nb065AlphaDummy096 x y))
          (Class.cv (nb065AlphaDummy097 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_100`. -/
@[expose]
noncomputable def nb065AlphaDummy100 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_101`. -/
@[expose]
noncomputable def nb065AlphaDummy101 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
      ((Class.cv (nb065AlphaDummy097 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_102`. -/
@[expose]
noncomputable def nb065AlphaDummy102 : Var :=
  (freshVar (((synCcompl (Class.cv (nb065AlphaDummy093)))).fv ∪
      ((synCcompl (Class.cv (nb065AlphaDummy094)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_103`. -/
@[expose]
noncomputable def nb065AlphaDummy103 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb065AlphaDummy096 x y)))).fv ∪
      ((synCcompl (Class.cv (nb065AlphaDummy097 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_104`. -/
@[expose]
noncomputable def nb065AlphaDummy104 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy093))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_105`. -/
@[expose]
noncomputable def nb065AlphaDummy105 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
      ((Class.cv (nb065AlphaDummy096 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_106`. -/
@[expose]
noncomputable def nb065AlphaDummy106 : Var :=
  (freshVar
    (((Class.cv (nb065AlphaDummy094))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_107`. -/
@[expose]
noncomputable def nb065AlphaDummy107 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb065AlphaDummy097 x y))).fv ∪
      ((Class.cv (nb065AlphaDummy097 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_108`. -/
@[expose]
noncomputable def nb065AlphaDummy108 : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy078)
          (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
            (Wff.classEq (Class.cv (nb065AlphaDummy078))
              (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy078)
          (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
            (Wff.classEq (Class.cv (nb065AlphaDummy078))
              (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_109`. -/
@[expose]
noncomputable def nb065AlphaDummy109 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb065AlphaDummy080 x y)
          (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
              (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy080 x y)
          (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
              (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_110`. -/
@[expose]
noncomputable def nb065AlphaDummy110 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb065AlphaDummy079))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_111`. -/
@[expose]
noncomputable def nb065AlphaDummy111 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb065AlphaDummy081 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_112`. -/
@[expose]
noncomputable def nb065AlphaDummy112 : Var :=
  (freshVar (((synCphi (Class.cv (nb065AlphaDummy079)))).fv ∪
      ((synCphi (Class.cv (nb065AlphaDummy079)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb065_alpha_dummy_113`. -/
@[expose]
noncomputable def nb065AlphaDummy113 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb065AlphaDummy081 x y)))).fv ∪
      ((synCphi (Class.cv (nb065AlphaDummy081 x y)))).fv) 0)

theorem nb065_fresh_000 :
    (nb065AlphaDummy036) ∉
      (((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb065AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb065_fresh_001 :
    (nb065AlphaDummy012) ∉
      (((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCphi (Class.cv (nb065AlphaDummy007))))))).fv ∪
        ((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCphi (Class.cv (nb065AlphaDummy007))))))).fv) :=
  by
  simpa only [nb065AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCphi (Class.cv (nb065AlphaDummy007))))))).fv ∪
        ((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCphi (Class.cv (nb065AlphaDummy007))))))).fv)
      0

theorem nb065_fresh_002 (r : Var) (a : Var) :
    (nb065AlphaDummy037 r a) ∉
      (((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb065AlphaDummy037] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb065_fresh_003 (r : Var) (a : Var) :
    (nb065AlphaDummy013 r a) ∉
      (((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCphi (Class.cv (nb065AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCphi (Class.cv (nb065AlphaDummy009 r a))))))).fv) :=
  by
  simpa only [nb065AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCphi (Class.cv (nb065AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCphi (Class.cv (nb065AlphaDummy009 r a))))))).fv)
      0

theorem nb065_fresh_004 :
    (nb065AlphaDummy048) ∉
      (((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCphi (Class.cv (nb065AlphaDummy043))))))).fv ∪
        ((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCphi (Class.cv (nb065AlphaDummy043))))))).fv) :=
  by
  simpa only [nb065AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCphi (Class.cv (nb065AlphaDummy043))))))).fv ∪
        ((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCphi (Class.cv (nb065AlphaDummy043))))))).fv)
      0

theorem nb065_fresh_005 :
    (nb065AlphaDummy072) ∉
      (((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb065AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb065_fresh_006 (x : Var) (y : Var) :
    (nb065AlphaDummy049 x y) ∉
      (((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCphi (Class.cv (nb065AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCphi (Class.cv (nb065AlphaDummy045 x y))))))).fv) :=
  by
  simpa only [nb065AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCphi (Class.cv (nb065AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCphi (Class.cv (nb065AlphaDummy045 x y))))))).fv)
      0

theorem nb065_fresh_007 (x : Var) (y : Var) :
    (nb065AlphaDummy073 x y) ∉
      (((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb065AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb065_fresh_008 :
    (nb065AlphaDummy108) ∉
      (((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb065AlphaDummy108] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb065_fresh_009 :
    (nb065AlphaDummy084) ∉
      (((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCphi (Class.cv (nb065AlphaDummy079))))))).fv ∪
        ((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCphi (Class.cv (nb065AlphaDummy079))))))).fv) :=
  by
  simpa only [nb065AlphaDummy084] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCphi (Class.cv (nb065AlphaDummy079))))))).fv ∪
        ((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCphi (Class.cv (nb065AlphaDummy079))))))).fv)
      0

theorem nb065_fresh_010 (x : Var) (y : Var) :
    (nb065AlphaDummy109 x y) ∉
      (((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb065AlphaDummy109] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb065_fresh_011 (x : Var) (y : Var) :
    (nb065AlphaDummy085 x y) ∉
      (((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCphi (Class.cv (nb065AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCphi (Class.cv (nb065AlphaDummy081 x y))))))).fv) :=
  by
  simpa only [nb065AlphaDummy085] using
    freshVar_not_mem
      (((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCphi (Class.cv (nb065AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCphi (Class.cv (nb065AlphaDummy081 x y))))))).fv)
      0

theorem nb065_fresh_012 :
    (nb065AlphaDummy006) ∉
      (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv) :=
  by
  simpa only [nb065AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv)
      0

theorem nb065_fresh_013 :
    (nb065AlphaDummy007) ∉
      (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv) :=
  by
  simpa only [nb065AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv)
      1

theorem nb065_distinct_014 : (nb065AlphaDummy006) ≠ (nb065AlphaDummy007) := by
  simpa only [nb065AlphaDummy006, nb065AlphaDummy007] using
    (freshVar_injective
      (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb065_fresh_015 :
    (nb065AlphaDummy042) ∉
      (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv) :=
  by
  simpa only [nb065AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv)
      0

theorem nb065_fresh_016 :
    (nb065AlphaDummy043) ∉
      (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv) :=
  by
  simpa only [nb065AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv)
      1

theorem nb065_distinct_017 : (nb065AlphaDummy042) ≠ (nb065AlphaDummy043) := by
  simpa only [nb065AlphaDummy042, nb065AlphaDummy043] using
    (freshVar_injective
      (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb065_fresh_018 :
    (nb065AlphaDummy078) ∉
      (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv) :=
  by
  simpa only [nb065AlphaDummy078] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv)
      0

theorem nb065_fresh_019 :
    (nb065AlphaDummy079) ∉
      (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv) :=
  by
  simpa only [nb065AlphaDummy079] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv)
      1

theorem nb065_distinct_020 : (nb065AlphaDummy078) ≠ (nb065AlphaDummy079) := by
  simpa only [nb065AlphaDummy078, nb065AlphaDummy079] using
    (freshVar_injective
      (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb065_fresh_021 :
    (nb065AlphaDummy014) ∉ (((Class.cv (nb065AlphaDummy007))).fv) := by
  simpa only [nb065AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy007))).fv) 0

theorem nb065_fresh_022 :
    (nb065AlphaDummy015) ∉ (((Class.cv (nb065AlphaDummy007))).fv) := by
  simpa only [nb065AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy007))).fv) 1

theorem nb065_distinct_023 : (nb065AlphaDummy014) ≠ (nb065AlphaDummy015) := by
  simpa only [nb065AlphaDummy014, nb065AlphaDummy015] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_024 (r : Var) (a : Var) :
    (nb065AlphaDummy016 r a) ∉ (((Class.cv (nb065AlphaDummy009 r a))).fv) := by
  simpa only [nb065AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy009 r a))).fv) 0

theorem nb065_fresh_025 (r : Var) (a : Var) :
    (nb065AlphaDummy017 r a) ∉ (((Class.cv (nb065AlphaDummy009 r a))).fv) := by
  simpa only [nb065AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy009 r a))).fv) 1

theorem nb065_distinct_026 (r : Var) (a : Var) :
    (nb065AlphaDummy016 r a) ≠ (nb065AlphaDummy017 r a) := by
  simpa only [nb065AlphaDummy016, nb065AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy009 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb065_fresh_027 :
    (nb065AlphaDummy020) ∉
      (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) 0

theorem nb065_fresh_028 :
    (nb065AlphaDummy021) ∉
      (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) 1

theorem nb065_fresh_029 :
    (nb065AlphaDummy022) ∉
      (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) 2

theorem nb065_distinct_030 : (nb065AlphaDummy020) ≠ (nb065AlphaDummy021) := by
  simpa only [nb065AlphaDummy020, nb065AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb065_distinct_031 : (nb065AlphaDummy020) ≠ (nb065AlphaDummy022) := by
  simpa only [nb065AlphaDummy020, nb065AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb065_distinct_032 : (nb065AlphaDummy021) ≠ (nb065AlphaDummy022) := by
  simpa only [nb065AlphaDummy021, nb065AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb065_fresh_033 (r : Var) (a : Var) :
    (nb065AlphaDummy023 r a) ∉
      (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 0

theorem nb065_fresh_034 (r : Var) (a : Var) :
    (nb065AlphaDummy024 r a) ∉
      (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 1

theorem nb065_fresh_035 (r : Var) (a : Var) :
    (nb065AlphaDummy025 r a) ∉
      (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) 2

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C065C001Part002`. -/


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

theorem nb065_distinct_036 (r : Var) (a : Var) :
    (nb065AlphaDummy023 r a) ≠ (nb065AlphaDummy024 r a) := by
  simpa only [nb065AlphaDummy023, nb065AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb065_distinct_037 (r : Var) (a : Var) :
    (nb065AlphaDummy023 r a) ≠ (nb065AlphaDummy025 r a) := by
  simpa only [nb065AlphaDummy023, nb065AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb065_distinct_038 (r : Var) (a : Var) :
    (nb065AlphaDummy024 r a) ≠ (nb065AlphaDummy025 r a) := by
  simpa only [nb065AlphaDummy024, nb065AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb065_fresh_039 :
    (nb065AlphaDummy032) ∉
      (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy021))).fv) :=
  by
  simpa only [nb065AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy021))).fv)
      0

theorem nb065_fresh_040 :
    (nb065AlphaDummy028) ∉
      (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv) :=
  by
  simpa only [nb065AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv)
      0

theorem nb065_fresh_041 :
    (nb065AlphaDummy034) ∉
      (((Class.cv (nb065AlphaDummy022))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv) :=
  by
  simpa only [nb065AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy022))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv)
      0

theorem nb065_fresh_042 (r : Var) (a : Var) :
    (nb065AlphaDummy033 r a) ∉
      (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy024 r a))).fv) :=
  by
  simpa only [nb065AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy024 r a))).fv)
      0

theorem nb065_fresh_043 (r : Var) (a : Var) :
    (nb065AlphaDummy029 r a) ∉
      (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy025 r a))).fv) :=
  by
  simpa only [nb065AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy025 r a))).fv)
      0

theorem nb065_fresh_044 (r : Var) (a : Var) :
    (nb065AlphaDummy035 r a) ∉
      (((Class.cv (nb065AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy025 r a))).fv) :=
  by
  simpa only [nb065AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy025 r a))).fv)
      0

theorem nb065_fresh_045 :
    (nb065AlphaDummy050) ∉ (((Class.cv (nb065AlphaDummy043))).fv) := by
  simpa only [nb065AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy043))).fv) 0

theorem nb065_fresh_046 :
    (nb065AlphaDummy051) ∉ (((Class.cv (nb065AlphaDummy043))).fv) := by
  simpa only [nb065AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy043))).fv) 1

theorem nb065_distinct_047 : (nb065AlphaDummy050) ≠ (nb065AlphaDummy051) := by
  simpa only [nb065AlphaDummy050, nb065AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy043))).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_048 (x : Var) (y : Var) :
    (nb065AlphaDummy052 x y) ∉ (((Class.cv (nb065AlphaDummy045 x y))).fv) := by
  simpa only [nb065AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy045 x y))).fv) 0

theorem nb065_fresh_049 (x : Var) (y : Var) :
    (nb065AlphaDummy053 x y) ∉ (((Class.cv (nb065AlphaDummy045 x y))).fv) := by
  simpa only [nb065AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy045 x y))).fv) 1

theorem nb065_distinct_050 (x : Var) (y : Var) :
    (nb065AlphaDummy052 x y) ≠ (nb065AlphaDummy053 x y) := by
  simpa only [nb065AlphaDummy052, nb065AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy045 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb065_fresh_051 :
    (nb065AlphaDummy056) ∉
      (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) 0

theorem nb065_fresh_052 :
    (nb065AlphaDummy057) ∉
      (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) 1

theorem nb065_fresh_053 :
    (nb065AlphaDummy058) ∉
      (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) 2

theorem nb065_distinct_054 : (nb065AlphaDummy056) ≠ (nb065AlphaDummy057) := by
  simpa only [nb065AlphaDummy056, nb065AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb065_distinct_055 : (nb065AlphaDummy056) ≠ (nb065AlphaDummy058) := by
  simpa only [nb065AlphaDummy056, nb065AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb065_distinct_056 : (nb065AlphaDummy057) ≠ (nb065AlphaDummy058) := by
  simpa only [nb065AlphaDummy057, nb065AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb065_fresh_057 (x : Var) (y : Var) :
    (nb065AlphaDummy059 x y) ∉
      (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb065_fresh_058 (x : Var) (y : Var) :
    (nb065AlphaDummy060 x y) ∉
      (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb065_fresh_059 (x : Var) (y : Var) :
    (nb065AlphaDummy061 x y) ∉
      (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb065_distinct_060 (x : Var) (y : Var) :
    (nb065AlphaDummy059 x y) ≠ (nb065AlphaDummy060 x y) := by
  simpa only [nb065AlphaDummy059, nb065AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb065_distinct_061 (x : Var) (y : Var) :
    (nb065AlphaDummy059 x y) ≠ (nb065AlphaDummy061 x y) := by
  simpa only [nb065AlphaDummy059, nb065AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb065_distinct_062 (x : Var) (y : Var) :
    (nb065AlphaDummy060 x y) ≠ (nb065AlphaDummy061 x y) := by
  simpa only [nb065AlphaDummy060, nb065AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb065_fresh_063 :
    (nb065AlphaDummy068) ∉
      (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy057))).fv) :=
  by
  simpa only [nb065AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy057))).fv)
      0

theorem nb065_fresh_064 :
    (nb065AlphaDummy064) ∉
      (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv) :=
  by
  simpa only [nb065AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv)
      0

theorem nb065_fresh_065 :
    (nb065AlphaDummy070) ∉
      (((Class.cv (nb065AlphaDummy058))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv) :=
  by
  simpa only [nb065AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy058))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv)
      0

theorem nb065_fresh_066 (x : Var) (y : Var) :
    (nb065AlphaDummy069 x y) ∉
      (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb065AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy060 x y))).fv)
      0

theorem nb065_fresh_067 (x : Var) (y : Var) :
    (nb065AlphaDummy065 x y) ∉
      (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb065AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy061 x y))).fv)
      0

theorem nb065_fresh_068 (x : Var) (y : Var) :
    (nb065AlphaDummy071 x y) ∉
      (((Class.cv (nb065AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb065AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy061 x y))).fv)
      0

theorem nb065_fresh_069 :
    (nb065AlphaDummy086) ∉ (((Class.cv (nb065AlphaDummy079))).fv) := by
  simpa only [nb065AlphaDummy086] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy079))).fv) 0

theorem nb065_fresh_070 :
    (nb065AlphaDummy087) ∉ (((Class.cv (nb065AlphaDummy079))).fv) := by
  simpa only [nb065AlphaDummy087] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy079))).fv) 1

theorem nb065_distinct_071 : (nb065AlphaDummy086) ≠ (nb065AlphaDummy087) := by
  simpa only [nb065AlphaDummy086, nb065AlphaDummy087] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy079))).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_072 (x : Var) (y : Var) :
    (nb065AlphaDummy088 x y) ∉ (((Class.cv (nb065AlphaDummy081 x y))).fv) := by
  simpa only [nb065AlphaDummy088] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy081 x y))).fv) 0

theorem nb065_fresh_073 (x : Var) (y : Var) :
    (nb065AlphaDummy089 x y) ∉ (((Class.cv (nb065AlphaDummy081 x y))).fv) := by
  simpa only [nb065AlphaDummy089] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy081 x y))).fv) 1

theorem nb065_distinct_074 (x : Var) (y : Var) :
    (nb065AlphaDummy088 x y) ≠ (nb065AlphaDummy089 x y) := by
  simpa only [nb065AlphaDummy088, nb065AlphaDummy089] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy081 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb065_fresh_075 :
    (nb065AlphaDummy092) ∉
      (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy092] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) 0

theorem nb065_fresh_076 :
    (nb065AlphaDummy093) ∉
      (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy093] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) 1

theorem nb065_fresh_077 :
    (nb065AlphaDummy094) ∉
      (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy094] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) 2

theorem nb065_distinct_078 : (nb065AlphaDummy092) ≠ (nb065AlphaDummy093) := by
  simpa only [nb065AlphaDummy092, nb065AlphaDummy093] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb065_distinct_079 : (nb065AlphaDummy092) ≠ (nb065AlphaDummy094) := by
  simpa only [nb065AlphaDummy092, nb065AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb065_distinct_080 : (nb065AlphaDummy093) ≠ (nb065AlphaDummy094) := by
  simpa only [nb065AlphaDummy093, nb065AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb065_fresh_081 (x : Var) (y : Var) :
    (nb065AlphaDummy095 x y) ∉
      (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy095] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb065_fresh_082 (x : Var) (y : Var) :
    (nb065AlphaDummy096 x y) ∉
      (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb065_fresh_083 (x : Var) (y : Var) :
    (nb065AlphaDummy097 x y) ∉
      (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb065AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb065_distinct_084 (x : Var) (y : Var) :
    (nb065AlphaDummy095 x y) ≠ (nb065AlphaDummy096 x y) := by
  simpa only [nb065AlphaDummy095, nb065AlphaDummy096] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb065_distinct_085 (x : Var) (y : Var) :
    (nb065AlphaDummy095 x y) ≠ (nb065AlphaDummy097 x y) := by
  simpa only [nb065AlphaDummy095, nb065AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb065_distinct_086 (x : Var) (y : Var) :
    (nb065AlphaDummy096 x y) ≠ (nb065AlphaDummy097 x y) := by
  simpa only [nb065AlphaDummy096, nb065AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb065_fresh_087 :
    (nb065AlphaDummy104) ∉
      (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy093))).fv) :=
  by
  simpa only [nb065AlphaDummy104] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy093))).fv)
      0

theorem nb065_fresh_088 :
    (nb065AlphaDummy100) ∉
      (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv) :=
  by
  simpa only [nb065AlphaDummy100] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv)
      0

theorem nb065_fresh_089 :
    (nb065AlphaDummy106) ∉
      (((Class.cv (nb065AlphaDummy094))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv) :=
  by
  simpa only [nb065AlphaDummy106] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy094))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv)
      0

theorem nb065_fresh_090 (x : Var) (y : Var) :
    (nb065AlphaDummy105 x y) ∉
      (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy096 x y))).fv) :=
  by
  simpa only [nb065AlphaDummy105] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy096 x y))).fv)
      0

theorem nb065_fresh_091 (x : Var) (y : Var) :
    (nb065AlphaDummy101 x y) ∉
      (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy097 x y))).fv) :=
  by
  simpa only [nb065AlphaDummy101] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy097 x y))).fv)
      0

theorem nb065_fresh_092 (x : Var) (y : Var) :
    (nb065AlphaDummy107 x y) ∉
      (((Class.cv (nb065AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy097 x y))).fv) :=
  by
  simpa only [nb065AlphaDummy107] using
    freshVar_not_mem
      (((Class.cv (nb065AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy097 x y))).fv)
      0

theorem nb065_fresh_093 (r : Var) (a : Var) :
    (nb065AlphaDummy008 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb065AlphaDummy008] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb065_fresh_094 (r : Var) (a : Var) :
    (nb065AlphaDummy009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb065AlphaDummy009] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb065_distinct_095 (r : Var) (a : Var) :
    (nb065AlphaDummy008 r a) ≠ (nb065AlphaDummy009 r a) := by
  simpa only [nb065AlphaDummy008, nb065AlphaDummy009] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_096 (x : Var) (y : Var) :
    (nb065AlphaDummy044 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb065AlphaDummy044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb065_fresh_097 (x : Var) (y : Var) :
    (nb065AlphaDummy045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb065AlphaDummy045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb065_distinct_098 (x : Var) (y : Var) :
    (nb065AlphaDummy044 x y) ≠ (nb065AlphaDummy045 x y) := by
  simpa only [nb065AlphaDummy044, nb065AlphaDummy045] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_099 (x : Var) (y : Var) :
    (nb065AlphaDummy080 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb065AlphaDummy080] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0

theorem nb065_fresh_100 (x : Var) (y : Var) :
    (nb065AlphaDummy081 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb065AlphaDummy081] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1

theorem nb065_distinct_101 (x : Var) (y : Var) :
    (nb065AlphaDummy080 x y) ≠ (nb065AlphaDummy081 x y) := by
  simpa only [nb065AlphaDummy080, nb065AlphaDummy081] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_102 :
    (nb065AlphaDummy018) ∉
      (((Wff.classMem (Class.cv (nb065AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy014))).fv) :=
  by
  simpa only [nb065AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb065AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy014))).fv)
      0

theorem nb065_fresh_103 (r : Var) (a : Var) :
    (nb065AlphaDummy019 r a) ∉
      (((Wff.classMem (Class.cv (nb065AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy016 r a))).fv) :=
  by
  simpa only [nb065AlphaDummy019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb065AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy016 r a))).fv)
      0

theorem nb065_fresh_104 :
    (nb065AlphaDummy054) ∉
      (((Wff.classMem (Class.cv (nb065AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy050))).fv) :=
  by
  simpa only [nb065AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb065AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy050))).fv)
      0

theorem nb065_fresh_105 (x : Var) (y : Var) :
    (nb065AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb065AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb065AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb065AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy052 x y))).fv)
      0

theorem nb065_fresh_106 :
    (nb065AlphaDummy090) ∉
      (((Wff.classMem (Class.cv (nb065AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy086))).fv) :=
  by
  simpa only [nb065AlphaDummy090] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb065AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy086))).fv)
      0

theorem nb065_fresh_107 (x : Var) (y : Var) :
    (nb065AlphaDummy091 x y) ∉
      (((Wff.classMem (Class.cv (nb065AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy088 x y))).fv) :=
  by
  simpa only [nb065AlphaDummy091] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb065AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy088 x y))).fv)
      0

theorem nb065_fresh_108 :
    (nb065AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb065AlphaDummy006)
              (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
                (Wff.classEq (Class.cv (nb065AlphaDummy006))
                  (synCphi (Class.cv (nb065AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy006)
              (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
                (Wff.classEq (Class.cv (nb065AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb065AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb065AlphaDummy006)
              (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
                (Wff.classEq (Class.cv (nb065AlphaDummy006))
                  (synCphi (Class.cv (nb065AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy006)
              (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
                (Wff.classEq (Class.cv (nb065AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb065_fresh_109 (r : Var) (a : Var) :
    (nb065AlphaDummy011 r a) ∉
      (((synCcompl (Class.cab (nb065AlphaDummy008 r a)
              (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                  (synCphi (Class.cv (nb065AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy008 r a)
              (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb065AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb065AlphaDummy008 r a)
              (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                  (synCphi (Class.cv (nb065AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy008 r a)
              (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb065_fresh_110 :
    (nb065AlphaDummy046) ∉
      (((synCcompl (Class.cab (nb065AlphaDummy042)
              (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
                (Wff.classEq (Class.cv (nb065AlphaDummy042))
                  (synCphi (Class.cv (nb065AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy042)
              (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
                (Wff.classEq (Class.cv (nb065AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb065AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb065AlphaDummy042)
              (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
                (Wff.classEq (Class.cv (nb065AlphaDummy042))
                  (synCphi (Class.cv (nb065AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy042)
              (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
                (Wff.classEq (Class.cv (nb065AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb065_fresh_111 (x : Var) (y : Var) :
    (nb065AlphaDummy047 x y) ∉
      (((synCcompl (Class.cab (nb065AlphaDummy044 x y)
              (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                  (synCphi (Class.cv (nb065AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy044 x y)
              (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb065AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb065AlphaDummy044 x y)
              (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                  (synCphi (Class.cv (nb065AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy044 x y)
              (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb065_fresh_112 :
    (nb065AlphaDummy082) ∉
      (((synCcompl (Class.cab (nb065AlphaDummy078)
              (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
                (Wff.classEq (Class.cv (nb065AlphaDummy078))
                  (synCphi (Class.cv (nb065AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy078)
              (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
                (Wff.classEq (Class.cv (nb065AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb065AlphaDummy082] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb065AlphaDummy078)
              (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
                (Wff.classEq (Class.cv (nb065AlphaDummy078))
                  (synCphi (Class.cv (nb065AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy078)
              (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
                (Wff.classEq (Class.cv (nb065AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb065_fresh_113 (x : Var) (y : Var) :
    (nb065AlphaDummy083 x y) ∉
      (((synCcompl (Class.cab (nb065AlphaDummy080 x y)
              (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                  (synCphi (Class.cv (nb065AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy080 x y)
              (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb065AlphaDummy083] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb065AlphaDummy080 x y)
              (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                  (synCphi (Class.cv (nb065AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy080 x y)
              (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb065_fresh_114 :
    (nb065AlphaDummy030) ∉
      (((synCcompl (Class.cv (nb065AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy022)))).fv) :=
  by
  simpa only [nb065AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb065AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy022)))).fv)
      0

theorem nb065_fresh_115 (r : Var) (a : Var) :
    (nb065AlphaDummy031 r a) ∉
      (((synCcompl (Class.cv (nb065AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy025 r a)))).fv) :=
  by
  simpa only [nb065AlphaDummy031] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb065AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy025 r a)))).fv)
      0

theorem nb065_fresh_116 :
    (nb065AlphaDummy066) ∉
      (((synCcompl (Class.cv (nb065AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy058)))).fv) :=
  by
  simpa only [nb065AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb065AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy058)))).fv)
      0

theorem nb065_fresh_117 (x : Var) (y : Var) :
    (nb065AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb065AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb065AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb065AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy061 x y)))).fv)
      0

theorem nb065_fresh_118 :
    (nb065AlphaDummy102) ∉
      (((synCcompl (Class.cv (nb065AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy094)))).fv) :=
  by
  simpa only [nb065AlphaDummy102] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb065AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy094)))).fv)
      0

theorem nb065_fresh_119 (x : Var) (y : Var) :
    (nb065AlphaDummy103 x y) ∉
      (((synCcompl (Class.cv (nb065AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy097 x y)))).fv) :=
  by
  simpa only [nb065AlphaDummy103] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb065AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy097 x y)))).fv)
      0

theorem nb065_fresh_120 :
    (nb065AlphaDummy038) ∉
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb065AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb065_fresh_121 (r : Var) (a : Var) :
    (nb065AlphaDummy039 r a) ∉
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb065AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb065_fresh_122 :
    (nb065AlphaDummy074) ∉
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb065AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb065_fresh_123 (x : Var) (y : Var) :
    (nb065AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb065AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb065_fresh_124 :
    (nb065AlphaDummy110) ∉
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb065AlphaDummy110] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb065_fresh_125 (x : Var) (y : Var) :
    (nb065AlphaDummy111 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb065AlphaDummy111] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb065_fresh_126 :
    (nb065AlphaDummy026) ∉
      (((synCnin (Class.cv (nb065AlphaDummy021)) (Class.cv (nb065AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy021))
            (Class.cv (nb065AlphaDummy022)))).fv) :=
  by
  simpa only [nb065AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb065AlphaDummy021)) (Class.cv (nb065AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy021)) (Class.cv (nb065AlphaDummy022)))).fv)
      0

theorem nb065_fresh_127 (r : Var) (a : Var) :
    (nb065AlphaDummy027 r a) ∉
      (((synCnin (Class.cv (nb065AlphaDummy024 r a))
            (Class.cv (nb065AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy024 r a))
            (Class.cv (nb065AlphaDummy025 r a)))).fv) :=
  by
  simpa only [nb065AlphaDummy027] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb065AlphaDummy024 r a))
            (Class.cv (nb065AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy024 r a))
            (Class.cv (nb065AlphaDummy025 r a)))).fv)
      0

theorem nb065_fresh_128 :
    (nb065AlphaDummy062) ∉
      (((synCnin (Class.cv (nb065AlphaDummy057)) (Class.cv (nb065AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy057))
            (Class.cv (nb065AlphaDummy058)))).fv) :=
  by
  simpa only [nb065AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb065AlphaDummy057)) (Class.cv (nb065AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy057)) (Class.cv (nb065AlphaDummy058)))).fv)
      0

theorem nb065_fresh_129 (x : Var) (y : Var) :
    (nb065AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb065AlphaDummy060 x y))
            (Class.cv (nb065AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy060 x y))
            (Class.cv (nb065AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb065AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb065AlphaDummy060 x y))
            (Class.cv (nb065AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy060 x y))
            (Class.cv (nb065AlphaDummy061 x y)))).fv)
      0

theorem nb065_fresh_130 :
    (nb065AlphaDummy098) ∉
      (((synCnin (Class.cv (nb065AlphaDummy093)) (Class.cv (nb065AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy093))
            (Class.cv (nb065AlphaDummy094)))).fv) :=
  by
  simpa only [nb065AlphaDummy098] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb065AlphaDummy093)) (Class.cv (nb065AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy093)) (Class.cv (nb065AlphaDummy094)))).fv)
      0

theorem nb065_fresh_131 (x : Var) (y : Var) :
    (nb065AlphaDummy099 x y) ∉
      (((synCnin (Class.cv (nb065AlphaDummy096 x y))
            (Class.cv (nb065AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy096 x y))
            (Class.cv (nb065AlphaDummy097 x y)))).fv) :=
  by
  simpa only [nb065AlphaDummy099] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb065AlphaDummy096 x y))
            (Class.cv (nb065AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy096 x y))
            (Class.cv (nb065AlphaDummy097 x y)))).fv)
      0

theorem nb065_fresh_132 :
    (nb065AlphaDummy040) ∉
      (((synCphi (Class.cv (nb065AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy007)))).fv) :=
  by
  simpa only [nb065AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb065AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy007)))).fv)
      0

theorem nb065_fresh_133 (r : Var) (a : Var) :
    (nb065AlphaDummy041 r a) ∉
      (((synCphi (Class.cv (nb065AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy009 r a)))).fv) :=
  by
  simpa only [nb065AlphaDummy041] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb065AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy009 r a)))).fv)
      0

theorem nb065_fresh_134 :
    (nb065AlphaDummy076) ∉
      (((synCphi (Class.cv (nb065AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy043)))).fv) :=
  by
  simpa only [nb065AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb065AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy043)))).fv)
      0

theorem nb065_fresh_135 (x : Var) (y : Var) :
    (nb065AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb065AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy045 x y)))).fv) :=
  by
  simpa only [nb065AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb065AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy045 x y)))).fv)
      0

theorem nb065_fresh_136 :
    (nb065AlphaDummy112) ∉
      (((synCphi (Class.cv (nb065AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy079)))).fv) :=
  by
  simpa only [nb065AlphaDummy112] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb065AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy079)))).fv)
      0

theorem nb065_fresh_137 (x : Var) (y : Var) :
    (nb065AlphaDummy113 x y) ∉
      (((synCphi (Class.cv (nb065AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy081 x y)))).fv) :=
  by
  simpa only [nb065AlphaDummy113] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb065AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy081 x y)))).fv)
      0

theorem nb065_fresh_138 :
    (nb065AlphaDummy004) ∉
      (({(nb065AlphaDummy001)} : Finset Var) ∪ ({(nb065AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb065AlphaDummy002) (Class.cv (nb065AlphaDummy000))
            (synWral (nb065AlphaDummy003) (Class.cv (nb065AlphaDummy000)) (Wff.imp
                (synWbr (Class.cv (nb065AlphaDummy002))
                  (Class.cv (nb065AlphaDummy001)) (Class.cv (nb065AlphaDummy003)))
                (synWbr (Class.cv (nb065AlphaDummy003)) (Class.cv (nb065AlphaDummy001))
                  (Class.cv (nb065AlphaDummy002))))))).fv) :=
  by
  simpa only [nb065AlphaDummy004] using
    freshVar_not_mem
      (({(nb065AlphaDummy001)} : Finset Var) ∪ ({(nb065AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb065AlphaDummy002) (Class.cv (nb065AlphaDummy000))
            (synWral (nb065AlphaDummy003) (Class.cv (nb065AlphaDummy000)) (Wff.imp
                (synWbr (Class.cv (nb065AlphaDummy002))
                  (Class.cv (nb065AlphaDummy001)) (Class.cv (nb065AlphaDummy003)))
                (synWbr (Class.cv (nb065AlphaDummy003)) (Class.cv (nb065AlphaDummy001))
                  (Class.cv (nb065AlphaDummy002))))))).fv)
      0

theorem nb065_fresh_139 (x : Var) (y : Var) (r : Var) (a : Var) :
    (nb065AlphaDummy005 x y r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (Wff.imp (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) :=
  by
  simpa only [nb065AlphaDummy005] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (Wff.imp (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv)
      0

theorem nb065_fresh_140 : (nb065AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb065AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb065_fresh_141 : (nb065AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb065AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb065_fresh_142 : (nb065AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb065AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb065_fresh_143 : (nb065AlphaDummy003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb065AlphaDummy003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb065_distinct_144 : (nb065AlphaDummy000) ≠ (nb065AlphaDummy001) := by
  simpa only [nb065AlphaDummy000, nb065AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb065_distinct_145 : (nb065AlphaDummy000) ≠ (nb065AlphaDummy002) := by
  simpa only [nb065AlphaDummy000, nb065AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb065_distinct_146 : (nb065AlphaDummy000) ≠ (nb065AlphaDummy003) := by
  simpa only [nb065AlphaDummy000, nb065AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb065_distinct_147 : (nb065AlphaDummy001) ≠ (nb065AlphaDummy002) := by
  simpa only [nb065AlphaDummy001, nb065AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb065_distinct_148 : (nb065AlphaDummy001) ≠ (nb065AlphaDummy003) := by
  simpa only [nb065AlphaDummy001, nb065AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb065_distinct_149 : (nb065AlphaDummy002) ≠ (nb065AlphaDummy003) := by
  simpa only [nb065AlphaDummy002, nb065AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb065_support_mem_0000 :
    (nb065AlphaDummy001) ∈
      (({(nb065AlphaDummy001)} : Finset Var) ∪ ({(nb065AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb065AlphaDummy002) (Class.cv (nb065AlphaDummy000))
            (synWral (nb065AlphaDummy003) (Class.cv (nb065AlphaDummy000)) (Wff.imp
                (synWbr (Class.cv (nb065AlphaDummy002))
                  (Class.cv (nb065AlphaDummy001)) (Class.cv (nb065AlphaDummy003)))
                (synWbr (Class.cv (nb065AlphaDummy003)) (Class.cv (nb065AlphaDummy001))
                  (Class.cv (nb065AlphaDummy002))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0001 (x : Var) (y : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (Wff.imp (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0002 :
    (nb065AlphaDummy000) ∈
      (({(nb065AlphaDummy001)} : Finset Var) ∪ ({(nb065AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb065AlphaDummy002) (Class.cv (nb065AlphaDummy000))
            (synWral (nb065AlphaDummy003) (Class.cv (nb065AlphaDummy000)) (Wff.imp
                (synWbr (Class.cv (nb065AlphaDummy002))
                  (Class.cv (nb065AlphaDummy001)) (Class.cv (nb065AlphaDummy003)))
                (synWbr (Class.cv (nb065AlphaDummy003)) (Class.cv (nb065AlphaDummy001))
                  (Class.cv (nb065AlphaDummy002))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0003 (x : Var) (y : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (Wff.imp (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                (synWbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0004 :
    (nb065AlphaDummy001) ∈
      (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0005 :
    (nb065AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb065AlphaDummy006)
              (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
                (Wff.classEq (Class.cv (nb065AlphaDummy006))
                  (synCphi (Class.cv (nb065AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy006)
              (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
                (Wff.classEq (Class.cv (nb065AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((synCcompl (Class.cab (nb065AlphaDummy008 r a)
              (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                  (synCphi (Class.cv (nb065AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy008 r a)
              (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0008 :
    (nb065AlphaDummy001) ∈
      (((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCphi (Class.cv (nb065AlphaDummy007))))))).fv ∪
        ((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCphi (Class.cv (nb065AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCphi (Class.cv (nb065AlphaDummy009 r a))))))).fv ∪
        ((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCphi (Class.cv (nb065AlphaDummy009 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0010 :
    (nb065AlphaDummy007) ∈ (((Class.cv (nb065AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0011 (r : Var) (a : Var) :
    (nb065AlphaDummy009 r a) ∈ (((Class.cv (nb065AlphaDummy009 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0012 :
    (nb065AlphaDummy014) ∈
      (((Wff.classMem (Class.cv (nb065AlphaDummy014)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy014)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy014))).fv) :=
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

theorem nb065_support_mem_0013 (r : Var) (a : Var) :
    (nb065AlphaDummy016 r a) ∈
      (((Wff.classMem (Class.cv (nb065AlphaDummy016 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy016 r a)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy016 r a))).fv) :=
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

theorem nb065_support_mem_0014 :
    (nb065AlphaDummy014) ∈
      (((Class.cv (nb065AlphaDummy014))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0015 (r : Var) (a : Var) :
    (nb065AlphaDummy016 r a) ∈
      (((Class.cv (nb065AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0016 :
    (nb065AlphaDummy021) ∈
      (((synCnin (Class.cv (nb065AlphaDummy021)) (Class.cv (nb065AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy021))
            (Class.cv (nb065AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0017 (r : Var) (a : Var) :
    (nb065AlphaDummy024 r a) ∈
      (((synCnin (Class.cv (nb065AlphaDummy024 r a))
            (Class.cv (nb065AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy024 r a))
            (Class.cv (nb065AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0018 :
    (nb065AlphaDummy021) ∈
      (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0019 (r : Var) (a : Var) :
    (nb065AlphaDummy024 r a) ∈
      (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0020 :
    (nb065AlphaDummy022) ∈
      (((synCnin (Class.cv (nb065AlphaDummy021)) (Class.cv (nb065AlphaDummy022)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy021))
            (Class.cv (nb065AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0021 (r : Var) (a : Var) :
    (nb065AlphaDummy025 r a) ∈
      (((synCnin (Class.cv (nb065AlphaDummy024 r a))
            (Class.cv (nb065AlphaDummy025 r a)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy024 r a))
            (Class.cv (nb065AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0022 :
    (nb065AlphaDummy022) ∈
      (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0023 (r : Var) (a : Var) :
    (nb065AlphaDummy025 r a) ∈
      (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0024 :
    (nb065AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0025 (r : Var) (a : Var) :
    (nb065AlphaDummy024 r a) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0026 :
    (nb065AlphaDummy021) ∈
      (((Class.cv (nb065AlphaDummy021))).fv ∪ ((Class.cv (nb065AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0027 (r : Var) (a : Var) :
    (nb065AlphaDummy024 r a) ∈
      (((Class.cv (nb065AlphaDummy024 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy024 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0028 :
    (nb065AlphaDummy022) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy021)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy022)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0029 (r : Var) (a : Var) :
    (nb065AlphaDummy025 r a) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy024 r a)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy025 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0030 :
    (nb065AlphaDummy022) ∈
      (((Class.cv (nb065AlphaDummy022))).fv ∪ ((Class.cv (nb065AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0031 (r : Var) (a : Var) :
    (nb065AlphaDummy025 r a) ∈
      (((Class.cv (nb065AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb065AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0032 :
    (nb065AlphaDummy000) ∈
      (((Class.cv (nb065AlphaDummy001))).fv ∪ ((Class.cv (nb065AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0033 :
    (nb065AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb065AlphaDummy006)
              (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy001))
                (Wff.classEq (Class.cv (nb065AlphaDummy006))
                  (synCphi (Class.cv (nb065AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy006)
              (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
                (Wff.classEq (Class.cv (nb065AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((synCcompl (Class.cab (nb065AlphaDummy008 r a)
              (synWrex (nb065AlphaDummy009 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                  (synCphi (Class.cv (nb065AlphaDummy009 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy008 r a)
              (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C065C001Part003`. -/


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

theorem nb065_support_mem_0036 :
    (nb065AlphaDummy000) ∈
      (((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy006)
            (synWrex (nb065AlphaDummy007) (Class.cv (nb065AlphaDummy000))
              (Wff.classEq (Class.cv (nb065AlphaDummy006))
                (synCun (synCphi (Class.cv (nb065AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy008 r a)
            (synWrex (nb065AlphaDummy009 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb065AlphaDummy008 r a))
                (synCun (synCphi (Class.cv (nb065AlphaDummy009 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0038 :
    (nb065AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0039 (r : Var) (a : Var) :
    (nb065AlphaDummy009 r a) ∈
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy009 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0040 :
    (nb065AlphaDummy007) ∈
      (((synCphi (Class.cv (nb065AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0041 (r : Var) (a : Var) :
    (nb065AlphaDummy009 r a) ∈
      (((synCphi (Class.cv (nb065AlphaDummy009 r a)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy009 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0042 :
    (nb065AlphaDummy002) ∈
      (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0043 :
    (nb065AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb065AlphaDummy042)
              (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
                (Wff.classEq (Class.cv (nb065AlphaDummy042))
                  (synCphi (Class.cv (nb065AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy042)
              (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
                (Wff.classEq (Class.cv (nb065AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0044 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0045 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb065AlphaDummy044 x y)
              (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                  (synCphi (Class.cv (nb065AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy044 x y)
              (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0046 :
    (nb065AlphaDummy002) ∈
      (((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCphi (Class.cv (nb065AlphaDummy043))))))).fv ∪
        ((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCphi (Class.cv (nb065AlphaDummy043))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0047 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCphi (Class.cv (nb065AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCphi (Class.cv (nb065AlphaDummy045 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0048 :
    (nb065AlphaDummy043) ∈ (((Class.cv (nb065AlphaDummy043))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0049 (x : Var) (y : Var) :
    (nb065AlphaDummy045 x y) ∈ (((Class.cv (nb065AlphaDummy045 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0050 :
    (nb065AlphaDummy050) ∈
      (((Wff.classMem (Class.cv (nb065AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy050))).fv) :=
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

theorem nb065_support_mem_0051 (x : Var) (y : Var) :
    (nb065AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb065AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy052 x y))).fv) :=
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

theorem nb065_support_mem_0052 :
    (nb065AlphaDummy050) ∈
      (((Class.cv (nb065AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0053 (x : Var) (y : Var) :
    (nb065AlphaDummy052 x y) ∈
      (((Class.cv (nb065AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0054 :
    (nb065AlphaDummy057) ∈
      (((synCnin (Class.cv (nb065AlphaDummy057)) (Class.cv (nb065AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy057))
            (Class.cv (nb065AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0055 (x : Var) (y : Var) :
    (nb065AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb065AlphaDummy060 x y))
            (Class.cv (nb065AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy060 x y))
            (Class.cv (nb065AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0056 :
    (nb065AlphaDummy057) ∈
      (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0057 (x : Var) (y : Var) :
    (nb065AlphaDummy060 x y) ∈
      (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0058 :
    (nb065AlphaDummy058) ∈
      (((synCnin (Class.cv (nb065AlphaDummy057)) (Class.cv (nb065AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy057))
            (Class.cv (nb065AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0059 (x : Var) (y : Var) :
    (nb065AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb065AlphaDummy060 x y))
            (Class.cv (nb065AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy060 x y))
            (Class.cv (nb065AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0060 :
    (nb065AlphaDummy058) ∈
      (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0061 (x : Var) (y : Var) :
    (nb065AlphaDummy061 x y) ∈
      (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0062 :
    (nb065AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0063 (x : Var) (y : Var) :
    (nb065AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0064 :
    (nb065AlphaDummy057) ∈
      (((Class.cv (nb065AlphaDummy057))).fv ∪ ((Class.cv (nb065AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0065 (x : Var) (y : Var) :
    (nb065AlphaDummy060 x y) ∈
      (((Class.cv (nb065AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0066 :
    (nb065AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0067 (x : Var) (y : Var) :
    (nb065AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0068 :
    (nb065AlphaDummy058) ∈
      (((Class.cv (nb065AlphaDummy058))).fv ∪ ((Class.cv (nb065AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0069 (x : Var) (y : Var) :
    (nb065AlphaDummy061 x y) ∈
      (((Class.cv (nb065AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0070 :
    (nb065AlphaDummy003) ∈
      (((Class.cv (nb065AlphaDummy002))).fv ∪ ((Class.cv (nb065AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0071 :
    (nb065AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb065AlphaDummy042)
              (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy002))
                (Wff.classEq (Class.cv (nb065AlphaDummy042))
                  (synCphi (Class.cv (nb065AlphaDummy043)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy042)
              (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
                (Wff.classEq (Class.cv (nb065AlphaDummy042))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0072 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0073 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb065AlphaDummy044 x y)
              (synWrex (nb065AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                  (synCphi (Class.cv (nb065AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy044 x y)
              (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0074 :
    (nb065AlphaDummy003) ∈
      (((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy042)
            (synWrex (nb065AlphaDummy043) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy042))
                (synCun (synCphi (Class.cv (nb065AlphaDummy043)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0075 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy044 x y)
            (synWrex (nb065AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0076 :
    (nb065AlphaDummy043) ∈
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy043))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0077 (x : Var) (y : Var) :
    (nb065AlphaDummy045 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0078 :
    (nb065AlphaDummy043) ∈
      (((synCphi (Class.cv (nb065AlphaDummy043)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy043)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0079 (x : Var) (y : Var) :
    (nb065AlphaDummy045 x y) ∈
      (((synCphi (Class.cv (nb065AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy045 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0080 :
    (nb065AlphaDummy003) ∈
      (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0081 :
    (nb065AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb065AlphaDummy078)
              (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
                (Wff.classEq (Class.cv (nb065AlphaDummy078))
                  (synCphi (Class.cv (nb065AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy078)
              (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
                (Wff.classEq (Class.cv (nb065AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0082 (x : Var) (y : Var) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0083 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb065AlphaDummy080 x y)
              (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                  (synCphi (Class.cv (nb065AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy080 x y)
              (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0082 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0082 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0084 :
    (nb065AlphaDummy003) ∈
      (((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCphi (Class.cv (nb065AlphaDummy079))))))).fv ∪
        ((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCphi (Class.cv (nb065AlphaDummy079))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0085 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCphi (Class.cv (nb065AlphaDummy081 x y))))))).fv ∪
        ((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCphi (Class.cv (nb065AlphaDummy081 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0082 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0082 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0086 :
    (nb065AlphaDummy079) ∈ (((Class.cv (nb065AlphaDummy079))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0087 (x : Var) (y : Var) :
    (nb065AlphaDummy081 x y) ∈ (((Class.cv (nb065AlphaDummy081 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0088 :
    (nb065AlphaDummy086) ∈
      (((Wff.classMem (Class.cv (nb065AlphaDummy086)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy086)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy086))).fv) :=
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

theorem nb065_support_mem_0089 (x : Var) (y : Var) :
    (nb065AlphaDummy088 x y) ∈
      (((Wff.classMem (Class.cv (nb065AlphaDummy088 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb065AlphaDummy088 x y)) (synC1c))).fv ∪
        ((Class.cv (nb065AlphaDummy088 x y))).fv) :=
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

theorem nb065_support_mem_0090 :
    (nb065AlphaDummy086) ∈
      (((Class.cv (nb065AlphaDummy086))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0091 (x : Var) (y : Var) :
    (nb065AlphaDummy088 x y) ∈
      (((Class.cv (nb065AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0092 :
    (nb065AlphaDummy093) ∈
      (((synCnin (Class.cv (nb065AlphaDummy093)) (Class.cv (nb065AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy093))
            (Class.cv (nb065AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0093 (x : Var) (y : Var) :
    (nb065AlphaDummy096 x y) ∈
      (((synCnin (Class.cv (nb065AlphaDummy096 x y))
            (Class.cv (nb065AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy096 x y))
            (Class.cv (nb065AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0094 :
    (nb065AlphaDummy093) ∈
      (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0095 (x : Var) (y : Var) :
    (nb065AlphaDummy096 x y) ∈
      (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0096 :
    (nb065AlphaDummy094) ∈
      (((synCnin (Class.cv (nb065AlphaDummy093)) (Class.cv (nb065AlphaDummy094)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy093))
            (Class.cv (nb065AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0097 (x : Var) (y : Var) :
    (nb065AlphaDummy097 x y) ∈
      (((synCnin (Class.cv (nb065AlphaDummy096 x y))
            (Class.cv (nb065AlphaDummy097 x y)))).fv ∪
        ((synCnin (Class.cv (nb065AlphaDummy096 x y))
            (Class.cv (nb065AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0098 :
    (nb065AlphaDummy094) ∈
      (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0099 (x : Var) (y : Var) :
    (nb065AlphaDummy097 x y) ∈
      (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0100 :
    (nb065AlphaDummy093) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0101 (x : Var) (y : Var) :
    (nb065AlphaDummy096 x y) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0102 :
    (nb065AlphaDummy093) ∈
      (((Class.cv (nb065AlphaDummy093))).fv ∪ ((Class.cv (nb065AlphaDummy093))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0103 (x : Var) (y : Var) :
    (nb065AlphaDummy096 x y) ∈
      (((Class.cv (nb065AlphaDummy096 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy096 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0104 :
    (nb065AlphaDummy094) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy093)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0105 (x : Var) (y : Var) :
    (nb065AlphaDummy097 x y) ∈
      (((synCcompl (Class.cv (nb065AlphaDummy096 x y)))).fv ∪
        ((synCcompl (Class.cv (nb065AlphaDummy097 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0106 :
    (nb065AlphaDummy094) ∈
      (((Class.cv (nb065AlphaDummy094))).fv ∪ ((Class.cv (nb065AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0107 (x : Var) (y : Var) :
    (nb065AlphaDummy097 x y) ∈
      (((Class.cv (nb065AlphaDummy097 x y))).fv ∪
        ((Class.cv (nb065AlphaDummy097 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0108 :
    (nb065AlphaDummy002) ∈
      (((Class.cv (nb065AlphaDummy003))).fv ∪ ((Class.cv (nb065AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0109 :
    (nb065AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb065AlphaDummy078)
              (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy003))
                (Wff.classEq (Class.cv (nb065AlphaDummy078))
                  (synCphi (Class.cv (nb065AlphaDummy079)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy078)
              (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
                (Wff.classEq (Class.cv (nb065AlphaDummy078))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0110 (x : Var) (y : Var) :
    x ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0111 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb065AlphaDummy080 x y)
              (synWrex (nb065AlphaDummy081 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                  (synCphi (Class.cv (nb065AlphaDummy081 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb065AlphaDummy080 x y)
              (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                  (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0110 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0110 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0112 :
    (nb065AlphaDummy002) ∈
      (((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy078)
            (synWrex (nb065AlphaDummy079) (Class.cv (nb065AlphaDummy002))
              (Wff.classEq (Class.cv (nb065AlphaDummy078))
                (synCun (synCphi (Class.cv (nb065AlphaDummy079)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0113 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb065AlphaDummy080 x y)
            (synWrex (nb065AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb065AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb065AlphaDummy081 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0110 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb065_support_mem_0110 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb065_support_mem_0114 :
    (nb065AlphaDummy079) ∈
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy079))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0115 (x : Var) (y : Var) :
    (nb065AlphaDummy081 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb065AlphaDummy081 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0116 :
    (nb065AlphaDummy079) ∈
      (((synCphi (Class.cv (nb065AlphaDummy079)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy079)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb065_support_mem_0117 (x : Var) (y : Var) :
    (nb065AlphaDummy081 x y) ∈
      (((synCphi (Class.cv (nb065AlphaDummy081 x y)))).fv ∪
        ((synCphi (Class.cv (nb065AlphaDummy081 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
