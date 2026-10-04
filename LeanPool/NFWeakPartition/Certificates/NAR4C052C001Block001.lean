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

/-! Certificates from `NAR4C052C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_000`. -/
@[expose]
noncomputable def nb052AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_001`. -/
@[expose]
noncomputable def nb052AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_002`. -/
@[expose]
noncomputable def nb052AlphaDummy002 : Var :=
  (freshVar (({(nb052AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
          ({(nb052AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCun (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_003`. -/
@[expose]
noncomputable def nb052AlphaDummy003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCun (Class.cv x) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_004`. -/
@[expose]
noncomputable def nb052AlphaDummy004 : Var :=
  (freshVar
    (({(nb052AlphaDummy000)} : Finset Var) ∪ ({(nb052AlphaDummy001)} : Finset Var) ∪
        ({(nb052AlphaDummy002)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv (nb052AlphaDummy000)) (synCvv))
            (Wff.classMem (Class.cv (nb052AlphaDummy001)) (synCvv)))
          (Wff.classEq (Class.cv (nb052AlphaDummy002))
            (synCun (Class.cv (nb052AlphaDummy000))
              (Class.cv (nb052AlphaDummy001)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_005`. -/
@[expose]
noncomputable def nb052AlphaDummy005 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb052AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
          (Wff.classEq (Class.cv (nb052AlphaDummy003 x y))
            (synCun (Class.cv x) (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_006`. -/
@[expose]
noncomputable def nb052AlphaDummy006 : Var :=
  (freshVar (((synCop (Class.cv (nb052AlphaDummy000))
          (Class.cv (nb052AlphaDummy001)))).fv ∪ ((Class.cv (nb052AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_007`. -/
@[expose]
noncomputable def nb052AlphaDummy007 : Var :=
  (freshVar (((synCop (Class.cv (nb052AlphaDummy000))
          (Class.cv (nb052AlphaDummy001)))).fv ∪ ((Class.cv (nb052AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_008`. -/
@[expose]
noncomputable def nb052AlphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb052AlphaDummy003 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_009`. -/
@[expose]
noncomputable def nb052AlphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb052AlphaDummy003 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_010`. -/
@[expose]
noncomputable def nb052AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb052AlphaDummy006)
            (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_011`. -/
@[expose]
noncomputable def nb052AlphaDummy011 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_012`. -/
@[expose]
noncomputable def nb052AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
            (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
            (Wff.classEq (Class.cv (nb052AlphaDummy006))
              (synCphi (Class.cv (nb052AlphaDummy007))))))).fv ∪
      ((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
            (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
            (Wff.classEq (Class.cv (nb052AlphaDummy006))
              (synCphi (Class.cv (nb052AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_013`. -/
@[expose]
noncomputable def nb052AlphaDummy013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb052AlphaDummy008 x y)
          (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
              (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv ∪
      ((Class.cab (nb052AlphaDummy008 x y)
          (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
              (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_014`. -/
@[expose]
noncomputable def nb052AlphaDummy014 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_015`. -/
@[expose]
noncomputable def nb052AlphaDummy015 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_016`. -/
@[expose]
noncomputable def nb052AlphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_017`. -/
@[expose]
noncomputable def nb052AlphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_018`. -/
@[expose]
noncomputable def nb052AlphaDummy018 : Var :=
  (freshVar (((synCcompl (Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCphi (Class.cv (nb052AlphaDummy015)))))))).fv ∪ ((synCcompl
          (Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_019`. -/
@[expose]
noncomputable def nb052AlphaDummy019 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCphi (Class.cv (nb052AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_020`. -/
@[expose]
noncomputable def nb052AlphaDummy020 : Var :=
  (freshVar (((Class.cab (nb052AlphaDummy014)
          (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
            (Wff.classEq (Class.cv (nb052AlphaDummy014))
              (synCphi (Class.cv (nb052AlphaDummy015))))))).fv ∪
      ((Class.cab (nb052AlphaDummy014)
          (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
            (Wff.classEq (Class.cv (nb052AlphaDummy014))
              (synCphi (Class.cv (nb052AlphaDummy015))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_021`. -/
@[expose]
noncomputable def nb052AlphaDummy021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb052AlphaDummy016 x y)
          (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
              (synCphi (Class.cv (nb052AlphaDummy017 x y))))))).fv ∪
      ((Class.cab (nb052AlphaDummy016 x y) (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
              (synCphi (Class.cv (nb052AlphaDummy017 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_022`. -/
@[expose]
noncomputable def nb052AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_023`. -/
@[expose]
noncomputable def nb052AlphaDummy023 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy015))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_024`. -/
@[expose]
noncomputable def nb052AlphaDummy024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_025`. -/
@[expose]
noncomputable def nb052AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy017 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_026`. -/
@[expose]
noncomputable def nb052AlphaDummy026 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb052AlphaDummy022)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb052AlphaDummy022)) (synC1c))).fv ∪
      ((Class.cv (nb052AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_027`. -/
@[expose]
noncomputable def nb052AlphaDummy027 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb052AlphaDummy024 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb052AlphaDummy024 x y)) (synC1c))).fv ∪
      ((Class.cv (nb052AlphaDummy024 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_028`. -/
@[expose]
noncomputable def nb052AlphaDummy028 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_029`. -/
@[expose]
noncomputable def nb052AlphaDummy029 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_030`. -/
@[expose]
noncomputable def nb052AlphaDummy030 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_031`. -/
@[expose]
noncomputable def nb052AlphaDummy031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_032`. -/
@[expose]
noncomputable def nb052AlphaDummy032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_033`. -/
@[expose]
noncomputable def nb052AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_034`. -/
@[expose]
noncomputable def nb052AlphaDummy034 : Var :=
  (freshVar (((synCnin (Class.cv (nb052AlphaDummy029))
          (Class.cv (nb052AlphaDummy030)))).fv ∪
      ((synCnin (Class.cv (nb052AlphaDummy029)) (Class.cv (nb052AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_035`. -/
@[expose]
noncomputable def nb052AlphaDummy035 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb052AlphaDummy032 x y))
          (Class.cv (nb052AlphaDummy033 x y)))).fv ∪
      ((synCnin (Class.cv (nb052AlphaDummy032 x y))
          (Class.cv (nb052AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_036`. -/
@[expose]
noncomputable def nb052AlphaDummy036 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_037`. -/
@[expose]
noncomputable def nb052AlphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb052AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_038`. -/
@[expose]
noncomputable def nb052AlphaDummy038 : Var :=
  (freshVar (((synCcompl (Class.cv (nb052AlphaDummy029)))).fv ∪
      ((synCcompl (Class.cv (nb052AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_039`. -/
@[expose]
noncomputable def nb052AlphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb052AlphaDummy032 x y)))).fv ∪
      ((synCcompl (Class.cv (nb052AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_040`. -/
@[expose]
noncomputable def nb052AlphaDummy040 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy029))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_041`. -/
@[expose]
noncomputable def nb052AlphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb052AlphaDummy032 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_042`. -/
@[expose]
noncomputable def nb052AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy030))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_043`. -/
@[expose]
noncomputable def nb052AlphaDummy043 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy033 x y))).fv ∪
      ((Class.cv (nb052AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_044`. -/
@[expose]
noncomputable def nb052AlphaDummy044 : Var :=
  (freshVar (((Class.cab (nb052AlphaDummy014)
          (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
            (Wff.classEq (Class.cv (nb052AlphaDummy014))
              (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy014)
          (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
            (Wff.classEq (Class.cv (nb052AlphaDummy014))
              (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_045`. -/
@[expose]
noncomputable def nb052AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb052AlphaDummy016 x y)
          (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy016 x y)
          (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_046`. -/
@[expose]
noncomputable def nb052AlphaDummy046 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb052AlphaDummy015))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_047`. -/
@[expose]
noncomputable def nb052AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb052AlphaDummy017 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_048`. -/
@[expose]
noncomputable def nb052AlphaDummy048 : Var :=
  (freshVar (((synCphi (Class.cv (nb052AlphaDummy015)))).fv ∪
      ((synCphi (Class.cv (nb052AlphaDummy015)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_049`. -/
@[expose]
noncomputable def nb052AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb052AlphaDummy017 x y)))).fv ∪
      ((synCphi (Class.cv (nb052AlphaDummy017 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_050`. -/
@[expose]
noncomputable def nb052AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_051`. -/
@[expose]
noncomputable def nb052AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_052`. -/
@[expose]
noncomputable def nb052AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy009 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_053`. -/
@[expose]
noncomputable def nb052AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy009 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_054`. -/
@[expose]
noncomputable def nb052AlphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb052AlphaDummy050)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb052AlphaDummy050)) (synC1c))).fv ∪
      ((Class.cv (nb052AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_055`. -/
@[expose]
noncomputable def nb052AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb052AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb052AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb052AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_056`. -/
@[expose]
noncomputable def nb052AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_057`. -/
@[expose]
noncomputable def nb052AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_058`. -/
@[expose]
noncomputable def nb052AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_059`. -/
@[expose]
noncomputable def nb052AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_060`. -/
@[expose]
noncomputable def nb052AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_061`. -/
@[expose]
noncomputable def nb052AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_062`. -/
@[expose]
noncomputable def nb052AlphaDummy062 : Var :=
  (freshVar (((synCnin (Class.cv (nb052AlphaDummy057))
          (Class.cv (nb052AlphaDummy058)))).fv ∪
      ((synCnin (Class.cv (nb052AlphaDummy057)) (Class.cv (nb052AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_063`. -/
@[expose]
noncomputable def nb052AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb052AlphaDummy060 x y))
          (Class.cv (nb052AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb052AlphaDummy060 x y))
          (Class.cv (nb052AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_064`. -/
@[expose]
noncomputable def nb052AlphaDummy064 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_065`. -/
@[expose]
noncomputable def nb052AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb052AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_066`. -/
@[expose]
noncomputable def nb052AlphaDummy066 : Var :=
  (freshVar (((synCcompl (Class.cv (nb052AlphaDummy057)))).fv ∪
      ((synCcompl (Class.cv (nb052AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_067`. -/
@[expose]
noncomputable def nb052AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb052AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb052AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_068`. -/
@[expose]
noncomputable def nb052AlphaDummy068 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_069`. -/
@[expose]
noncomputable def nb052AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb052AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_070`. -/
@[expose]
noncomputable def nb052AlphaDummy070 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy058))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_071`. -/
@[expose]
noncomputable def nb052AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb052AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb052AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_072`. -/
@[expose]
noncomputable def nb052AlphaDummy072 : Var :=
  (freshVar (((Class.cab (nb052AlphaDummy006)
          (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
            (Wff.classEq (Class.cv (nb052AlphaDummy006))
              (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy006)
          (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
            (Wff.classEq (Class.cv (nb052AlphaDummy006))
              (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_073`. -/
@[expose]
noncomputable def nb052AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb052AlphaDummy008 x y)
          (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy008 x y)
          (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_074`. -/
@[expose]
noncomputable def nb052AlphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb052AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_075`. -/
@[expose]
noncomputable def nb052AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb052AlphaDummy009 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_076`. -/
@[expose]
noncomputable def nb052AlphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv (nb052AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb052AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_077`. -/
@[expose]
noncomputable def nb052AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb052AlphaDummy009 x y)))).fv ∪
      ((synCphi (Class.cv (nb052AlphaDummy009 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_078`. -/
@[expose]
noncomputable def nb052AlphaDummy078 : Var :=
  (freshVar (((synCcompl (Class.cv (nb052AlphaDummy000)))).fv ∪
      ((synCcompl (Class.cv (nb052AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_079`. -/
@[expose]
noncomputable def nb052AlphaDummy079 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv x))).fv ∪ ((synCcompl (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_080`. -/
@[expose]
noncomputable def nb052AlphaDummy080 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_081`. -/
@[expose]
noncomputable def nb052AlphaDummy081 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_082`. -/
@[expose]
noncomputable def nb052AlphaDummy082 : Var :=
  (freshVar
    (((Class.cv (nb052AlphaDummy001))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb052_alpha_dummy_083`. -/
@[expose]
noncomputable def nb052AlphaDummy083 (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0)

theorem nb052_fresh_000 :
    (nb052AlphaDummy072) ∉
      (((Class.cab (nb052AlphaDummy006)
            (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy006)
            (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb052AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb052AlphaDummy006)
            (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy006)
            (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb052_fresh_001 :
    (nb052AlphaDummy012) ∉
      (((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007))))))).fv ∪
        ((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007))))))).fv) :=
  by
  simpa only [nb052AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007))))))).fv ∪
        ((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007))))))).fv)
      0

theorem nb052_fresh_002 (x : Var) (y : Var) :
    (nb052AlphaDummy073 x y) ∉
      (((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb052AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb052_fresh_003 (x : Var) (y : Var) :
    (nb052AlphaDummy013 x y) ∉
      (((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv) :=
  by
  simpa only [nb052AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv)
      0

theorem nb052_fresh_004 :
    (nb052AlphaDummy020) ∉
      (((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCphi (Class.cv (nb052AlphaDummy015))))))).fv ∪
        ((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCphi (Class.cv (nb052AlphaDummy015))))))).fv) :=
  by
  simpa only [nb052AlphaDummy020] using
    freshVar_not_mem
      (((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCphi (Class.cv (nb052AlphaDummy015))))))).fv ∪
        ((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCphi (Class.cv (nb052AlphaDummy015))))))).fv)
      0

theorem nb052_fresh_005 :
    (nb052AlphaDummy044) ∉
      (((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb052AlphaDummy044] using
    freshVar_not_mem
      (((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb052_fresh_006 (x : Var) (y : Var) :
    (nb052AlphaDummy021 x y) ∉
      (((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCphi (Class.cv (nb052AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCphi (Class.cv (nb052AlphaDummy017 x y))))))).fv) :=
  by
  simpa only [nb052AlphaDummy021] using
    freshVar_not_mem
      (((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCphi (Class.cv (nb052AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCphi (Class.cv (nb052AlphaDummy017 x y))))))).fv)
      0

theorem nb052_fresh_007 (x : Var) (y : Var) :
    (nb052AlphaDummy045 x y) ∉
      (((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb052AlphaDummy045] using
    freshVar_not_mem
      (((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb052_fresh_008 :
    (nb052AlphaDummy080) ∉
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy000))).fv) :=
  by
  simpa only [nb052AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy000))).fv)
      0

theorem nb052_fresh_009 :
    (nb052AlphaDummy014) ∉
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) :=
  by
  simpa only [nb052AlphaDummy014] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv)
      0

theorem nb052_fresh_010 :
    (nb052AlphaDummy015) ∉
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) :=
  by
  simpa only [nb052AlphaDummy015] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv)
      1

theorem nb052_distinct_011 : (nb052AlphaDummy014) ≠ (nb052AlphaDummy015) := by
  simpa only [nb052AlphaDummy014, nb052AlphaDummy015] using
    (freshVar_injective
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb052_fresh_012 :
    (nb052AlphaDummy082) ∉
      (((Class.cv (nb052AlphaDummy001))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) :=
  by
  simpa only [nb052AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy001))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv)
      0

theorem nb052_fresh_013 :
    (nb052AlphaDummy050) ∉ (((Class.cv (nb052AlphaDummy007))).fv) := by
  simpa only [nb052AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy007))).fv) 0

theorem nb052_fresh_014 :
    (nb052AlphaDummy051) ∉ (((Class.cv (nb052AlphaDummy007))).fv) := by
  simpa only [nb052AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy007))).fv) 1

theorem nb052_distinct_015 : (nb052AlphaDummy050) ≠ (nb052AlphaDummy051) := by
  simpa only [nb052AlphaDummy050, nb052AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb052_fresh_016 (x : Var) (y : Var) :
    (nb052AlphaDummy052 x y) ∉ (((Class.cv (nb052AlphaDummy009 x y))).fv) := by
  simpa only [nb052AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy009 x y))).fv) 0

theorem nb052_fresh_017 (x : Var) (y : Var) :
    (nb052AlphaDummy053 x y) ∉ (((Class.cv (nb052AlphaDummy009 x y))).fv) := by
  simpa only [nb052AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy009 x y))).fv) 1

theorem nb052_distinct_018 (x : Var) (y : Var) :
    (nb052AlphaDummy052 x y) ≠ (nb052AlphaDummy053 x y) := by
  simpa only [nb052AlphaDummy052, nb052AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy009 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb052_fresh_019 :
    (nb052AlphaDummy022) ∉ (((Class.cv (nb052AlphaDummy015))).fv) := by
  simpa only [nb052AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy015))).fv) 0

theorem nb052_fresh_020 :
    (nb052AlphaDummy023) ∉ (((Class.cv (nb052AlphaDummy015))).fv) := by
  simpa only [nb052AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy015))).fv) 1

theorem nb052_distinct_021 : (nb052AlphaDummy022) ≠ (nb052AlphaDummy023) := by
  simpa only [nb052AlphaDummy022, nb052AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy015))).fv) (i := 0) (j := 1) (by decide))

theorem nb052_fresh_022 (x : Var) (y : Var) :
    (nb052AlphaDummy024 x y) ∉ (((Class.cv (nb052AlphaDummy017 x y))).fv) := by
  simpa only [nb052AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy017 x y))).fv) 0

theorem nb052_fresh_023 (x : Var) (y : Var) :
    (nb052AlphaDummy025 x y) ∉ (((Class.cv (nb052AlphaDummy017 x y))).fv) := by
  simpa only [nb052AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy017 x y))).fv) 1

theorem nb052_distinct_024 (x : Var) (y : Var) :
    (nb052AlphaDummy024 x y) ≠ (nb052AlphaDummy025 x y) := by
  simpa only [nb052AlphaDummy024, nb052AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy017 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb052_fresh_025 :
    (nb052AlphaDummy028) ∉
      (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) 0

theorem nb052_fresh_026 :
    (nb052AlphaDummy029) ∉
      (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) 1

theorem nb052_fresh_027 :
    (nb052AlphaDummy030) ∉
      (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) 2

theorem nb052_distinct_028 : (nb052AlphaDummy028) ≠ (nb052AlphaDummy029) := by
  simpa only [nb052AlphaDummy028, nb052AlphaDummy029] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb052_distinct_029 : (nb052AlphaDummy028) ≠ (nb052AlphaDummy030) := by
  simpa only [nb052AlphaDummy028, nb052AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb052_distinct_030 : (nb052AlphaDummy029) ≠ (nb052AlphaDummy030) := by
  simpa only [nb052AlphaDummy029, nb052AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb052_fresh_031 (x : Var) (y : Var) :
    (nb052AlphaDummy031 x y) ∉
      (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb052_fresh_032 (x : Var) (y : Var) :
    (nb052AlphaDummy032 x y) ∉
      (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb052_fresh_033 (x : Var) (y : Var) :
    (nb052AlphaDummy033 x y) ∉
      (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb052_distinct_034 (x : Var) (y : Var) :
    (nb052AlphaDummy031 x y) ≠ (nb052AlphaDummy032 x y) := by
  simpa only [nb052AlphaDummy031, nb052AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb052_distinct_035 (x : Var) (y : Var) :
    (nb052AlphaDummy031 x y) ≠ (nb052AlphaDummy033 x y) := by
  simpa only [nb052AlphaDummy031, nb052AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb052_distinct_036 (x : Var) (y : Var) :
    (nb052AlphaDummy032 x y) ≠ (nb052AlphaDummy033 x y) := by
  simpa only [nb052AlphaDummy032, nb052AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb052_fresh_037 :
    (nb052AlphaDummy040) ∉
      (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy029))).fv) :=
  by
  simpa only [nb052AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy029))).fv)
      0

theorem nb052_fresh_038 :
    (nb052AlphaDummy036) ∉
      (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv) :=
  by
  simpa only [nb052AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv)
      0

theorem nb052_fresh_039 :
    (nb052AlphaDummy042) ∉
      (((Class.cv (nb052AlphaDummy030))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv) :=
  by
  simpa only [nb052AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy030))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv)
      0

theorem nb052_fresh_040 (x : Var) (y : Var) :
    (nb052AlphaDummy041 x y) ∉
      (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy032 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy032 x y))).fv)
      0

theorem nb052_fresh_041 (x : Var) (y : Var) :
    (nb052AlphaDummy037 x y) ∉
      (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy033 x y))).fv)
      0

theorem nb052_fresh_042 (x : Var) (y : Var) :
    (nb052AlphaDummy043 x y) ∉
      (((Class.cv (nb052AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy033 x y))).fv)
      0

theorem nb052_fresh_043 :
    (nb052AlphaDummy056) ∉
      (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) 0

theorem nb052_fresh_044 :
    (nb052AlphaDummy057) ∉
      (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) 1

theorem nb052_fresh_045 :
    (nb052AlphaDummy058) ∉
      (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) 2

theorem nb052_distinct_046 : (nb052AlphaDummy056) ≠ (nb052AlphaDummy057) := by
  simpa only [nb052AlphaDummy056, nb052AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb052_distinct_047 : (nb052AlphaDummy056) ≠ (nb052AlphaDummy058) := by
  simpa only [nb052AlphaDummy056, nb052AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb052_distinct_048 : (nb052AlphaDummy057) ≠ (nb052AlphaDummy058) := by
  simpa only [nb052AlphaDummy057, nb052AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb052_fresh_049 (x : Var) (y : Var) :
    (nb052AlphaDummy059 x y) ∉
      (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb052_fresh_050 (x : Var) (y : Var) :
    (nb052AlphaDummy060 x y) ∉
      (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb052_fresh_051 (x : Var) (y : Var) :
    (nb052AlphaDummy061 x y) ∉
      (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb052AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb052_distinct_052 (x : Var) (y : Var) :
    (nb052AlphaDummy059 x y) ≠ (nb052AlphaDummy060 x y) := by
  simpa only [nb052AlphaDummy059, nb052AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb052_distinct_053 (x : Var) (y : Var) :
    (nb052AlphaDummy059 x y) ≠ (nb052AlphaDummy061 x y) := by
  simpa only [nb052AlphaDummy059, nb052AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb052_distinct_054 (x : Var) (y : Var) :
    (nb052AlphaDummy060 x y) ≠ (nb052AlphaDummy061 x y) := by
  simpa only [nb052AlphaDummy060, nb052AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb052_fresh_055 :
    (nb052AlphaDummy068) ∉
      (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy057))).fv) :=
  by
  simpa only [nb052AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy057))).fv)
      0

theorem nb052_fresh_056 :
    (nb052AlphaDummy064) ∉
      (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv) :=
  by
  simpa only [nb052AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv)
      0

theorem nb052_fresh_057 :
    (nb052AlphaDummy070) ∉
      (((Class.cv (nb052AlphaDummy058))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv) :=
  by
  simpa only [nb052AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy058))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv)
      0

theorem nb052_fresh_058 (x : Var) (y : Var) :
    (nb052AlphaDummy069 x y) ∉
      (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy060 x y))).fv)
      0

theorem nb052_fresh_059 (x : Var) (y : Var) :
    (nb052AlphaDummy065 x y) ∉
      (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy061 x y))).fv)
      0

theorem nb052_fresh_060 (x : Var) (y : Var) :
    (nb052AlphaDummy071 x y) ∉
      (((Class.cv (nb052AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb052AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy061 x y))).fv)
      0

theorem nb052_fresh_061 (x : Var) :
    (nb052AlphaDummy081 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb052AlphaDummy081] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0

theorem nb052_fresh_062 (x : Var) (y : Var) :
    (nb052AlphaDummy016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb052AlphaDummy016] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb052_fresh_063 (x : Var) (y : Var) :
    (nb052AlphaDummy017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb052AlphaDummy017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb052_distinct_064 (x : Var) (y : Var) :
    (nb052AlphaDummy016 x y) ≠ (nb052AlphaDummy017 x y) := by
  simpa only [nb052AlphaDummy016, nb052AlphaDummy017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb052_fresh_065 (y : Var) :
    (nb052AlphaDummy083 y) ∉ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb052AlphaDummy083] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C052C001Part002`. -/


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

theorem nb052_fresh_066 :
    (nb052AlphaDummy026) ∉
      (((Wff.classMem (Class.cv (nb052AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy022))).fv) :=
  by
  simpa only [nb052AlphaDummy026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb052AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy022))).fv)
      0

theorem nb052_fresh_067 (x : Var) (y : Var) :
    (nb052AlphaDummy027 x y) ∉
      (((Wff.classMem (Class.cv (nb052AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy024 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb052AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy024 x y))).fv)
      0

theorem nb052_fresh_068 :
    (nb052AlphaDummy054) ∉
      (((Wff.classMem (Class.cv (nb052AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy050))).fv) :=
  by
  simpa only [nb052AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb052AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy050))).fv)
      0

theorem nb052_fresh_069 (x : Var) (y : Var) :
    (nb052AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb052AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb052AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy052 x y))).fv)
      0

theorem nb052_fresh_070 :
    (nb052AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
                (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCphi (Class.cv (nb052AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy006)
              (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb052AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
                (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCphi (Class.cv (nb052AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy006)
              (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb052_fresh_071 (x : Var) (y : Var) :
    (nb052AlphaDummy011 x y) ∉
      (((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb052AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb052_fresh_072 :
    (nb052AlphaDummy018) ∉
      (((synCcompl (Class.cab (nb052AlphaDummy014)
              (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
                (Wff.classEq (Class.cv (nb052AlphaDummy014))
                  (synCphi (Class.cv (nb052AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy014)
              (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
                (Wff.classEq (Class.cv (nb052AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb052AlphaDummy018] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb052AlphaDummy014)
              (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
                (Wff.classEq (Class.cv (nb052AlphaDummy014))
                  (synCphi (Class.cv (nb052AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy014)
              (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
                (Wff.classEq (Class.cv (nb052AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb052_fresh_073 (x : Var) (y : Var) :
    (nb052AlphaDummy019 x y) ∉
      (((synCcompl (Class.cab (nb052AlphaDummy016 x y)
              (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                  (synCphi (Class.cv (nb052AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy016 x y)
              (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb052AlphaDummy019] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb052AlphaDummy016 x y)
              (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                  (synCphi (Class.cv (nb052AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy016 x y)
              (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb052_fresh_074 :
    (nb052AlphaDummy078) ∉
      (((synCcompl (Class.cv (nb052AlphaDummy000)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy001)))).fv) :=
  by
  simpa only [nb052AlphaDummy078] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb052AlphaDummy000)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy001)))).fv)
      0

theorem nb052_fresh_075 :
    (nb052AlphaDummy038) ∉
      (((synCcompl (Class.cv (nb052AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy030)))).fv) :=
  by
  simpa only [nb052AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb052AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy030)))).fv)
      0

theorem nb052_fresh_076 (x : Var) (y : Var) :
    (nb052AlphaDummy039 x y) ∉
      (((synCcompl (Class.cv (nb052AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb052AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb052AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy033 x y)))).fv)
      0

theorem nb052_fresh_077 :
    (nb052AlphaDummy066) ∉
      (((synCcompl (Class.cv (nb052AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy058)))).fv) :=
  by
  simpa only [nb052AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb052AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy058)))).fv)
      0

theorem nb052_fresh_078 (x : Var) (y : Var) :
    (nb052AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb052AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb052AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb052AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy061 x y)))).fv)
      0

theorem nb052_fresh_079 (x : Var) (y : Var) :
    (nb052AlphaDummy079 x y) ∉
      (((synCcompl (Class.cv x))).fv ∪ ((synCcompl (Class.cv y))).fv) :=
  by
  simpa only [nb052AlphaDummy079] using
    freshVar_not_mem (((synCcompl (Class.cv x))).fv ∪ ((synCcompl (Class.cv y))).fv) 0

theorem nb052_fresh_080 :
    (nb052AlphaDummy074) ∉
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb052AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb052_fresh_081 (x : Var) (y : Var) :
    (nb052AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb052AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb052_fresh_082 :
    (nb052AlphaDummy046) ∉
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb052AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb052_fresh_083 (x : Var) (y : Var) :
    (nb052AlphaDummy047 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb052AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb052_fresh_084 :
    (nb052AlphaDummy034) ∉
      (((synCnin (Class.cv (nb052AlphaDummy029)) (Class.cv (nb052AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy029))
            (Class.cv (nb052AlphaDummy030)))).fv) :=
  by
  simpa only [nb052AlphaDummy034] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb052AlphaDummy029)) (Class.cv (nb052AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy029)) (Class.cv (nb052AlphaDummy030)))).fv)
      0

theorem nb052_fresh_085 (x : Var) (y : Var) :
    (nb052AlphaDummy035 x y) ∉
      (((synCnin (Class.cv (nb052AlphaDummy032 x y))
            (Class.cv (nb052AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy032 x y))
            (Class.cv (nb052AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb052AlphaDummy035] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb052AlphaDummy032 x y))
            (Class.cv (nb052AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy032 x y))
            (Class.cv (nb052AlphaDummy033 x y)))).fv)
      0

theorem nb052_fresh_086 :
    (nb052AlphaDummy062) ∉
      (((synCnin (Class.cv (nb052AlphaDummy057)) (Class.cv (nb052AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy057))
            (Class.cv (nb052AlphaDummy058)))).fv) :=
  by
  simpa only [nb052AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb052AlphaDummy057)) (Class.cv (nb052AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy057)) (Class.cv (nb052AlphaDummy058)))).fv)
      0

theorem nb052_fresh_087 (x : Var) (y : Var) :
    (nb052AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb052AlphaDummy060 x y))
            (Class.cv (nb052AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy060 x y))
            (Class.cv (nb052AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb052AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb052AlphaDummy060 x y))
            (Class.cv (nb052AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy060 x y))
            (Class.cv (nb052AlphaDummy061 x y)))).fv)
      0

theorem nb052_fresh_088 :
    (nb052AlphaDummy006) ∉
      (((synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv ∪
        ((Class.cv (nb052AlphaDummy002))).fv) :=
  by
  simpa only [nb052AlphaDummy006] using
    freshVar_not_mem
      (((synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv ∪
        ((Class.cv (nb052AlphaDummy002))).fv)
      0

theorem nb052_fresh_089 :
    (nb052AlphaDummy007) ∉
      (((synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv ∪
        ((Class.cv (nb052AlphaDummy002))).fv) :=
  by
  simpa only [nb052AlphaDummy007] using
    freshVar_not_mem
      (((synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv ∪
        ((Class.cv (nb052AlphaDummy002))).fv)
      1

theorem nb052_distinct_090 : (nb052AlphaDummy006) ≠ (nb052AlphaDummy007) := by
  simpa only [nb052AlphaDummy006, nb052AlphaDummy007] using
    (freshVar_injective (((synCop (Class.cv (nb052AlphaDummy000))
            (Class.cv (nb052AlphaDummy001)))).fv ∪ ((Class.cv (nb052AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb052_fresh_091 (x : Var) (y : Var) :
    (nb052AlphaDummy008 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy008] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb052AlphaDummy003 x y))).fv)
      0

theorem nb052_fresh_092 (x : Var) (y : Var) :
    (nb052AlphaDummy009 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb052AlphaDummy009] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb052AlphaDummy003 x y))).fv)
      1

theorem nb052_distinct_093 (x : Var) (y : Var) :
    (nb052AlphaDummy008 x y) ≠ (nb052AlphaDummy009 x y) := by
  simpa only [nb052AlphaDummy008, nb052AlphaDummy009] using
    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052AlphaDummy003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb052_fresh_094 :
    (nb052AlphaDummy076) ∉
      (((synCphi (Class.cv (nb052AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy007)))).fv) :=
  by
  simpa only [nb052AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb052AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy007)))).fv)
      0

theorem nb052_fresh_095 (x : Var) (y : Var) :
    (nb052AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb052AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy009 x y)))).fv) :=
  by
  simpa only [nb052AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb052AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy009 x y)))).fv)
      0

theorem nb052_fresh_096 :
    (nb052AlphaDummy048) ∉
      (((synCphi (Class.cv (nb052AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy015)))).fv) :=
  by
  simpa only [nb052AlphaDummy048] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb052AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy015)))).fv)
      0

theorem nb052_fresh_097 (x : Var) (y : Var) :
    (nb052AlphaDummy049 x y) ∉
      (((synCphi (Class.cv (nb052AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy017 x y)))).fv) :=
  by
  simpa only [nb052AlphaDummy049] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb052AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy017 x y)))).fv)
      0

theorem nb052_fresh_098 :
    (nb052AlphaDummy002) ∉
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb052AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCun (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv) :=
  by
  simpa only [nb052AlphaDummy002] using
    freshVar_not_mem
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb052AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCun (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv)
      0

theorem nb052_fresh_099 :
    (nb052AlphaDummy004) ∉
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ({(nb052AlphaDummy001)} : Finset Var) ∪
          ({(nb052AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb052AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb052AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy002))
              (synCun (Class.cv (nb052AlphaDummy000))
                (Class.cv (nb052AlphaDummy001)))))).fv) :=
  by
  simpa only [nb052AlphaDummy004] using
    freshVar_not_mem
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ({(nb052AlphaDummy001)} : Finset Var) ∪
          ({(nb052AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb052AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb052AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy002))
              (synCun (Class.cv (nb052AlphaDummy000))
                (Class.cv (nb052AlphaDummy001)))))).fv)
      0

theorem nb052_fresh_100 (x : Var) (y : Var) :
    (nb052AlphaDummy003 x y) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCun (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb052AlphaDummy003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCun (Class.cv x) (Class.cv y))).fv)
      0

theorem nb052_fresh_101 (x : Var) (y : Var) :
    (nb052AlphaDummy005 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy003 x y))
              (synCun (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb052AlphaDummy005] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy003 x y))
              (synCun (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb052_fresh_102 : (nb052AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb052AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb052_fresh_103 : (nb052AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb052AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb052_distinct_104 : (nb052AlphaDummy000) ≠ (nb052AlphaDummy001) := by
  simpa only [nb052AlphaDummy000, nb052AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb052_support_mem_0000 :
    (nb052AlphaDummy000) ∈
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ({(nb052AlphaDummy001)} : Finset Var) ∪
          ({(nb052AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb052AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb052AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy002))
              (synCun (Class.cv (nb052AlphaDummy000))
                (Class.cv (nb052AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy003 x y))
              (synCun (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0002 :
    (nb052AlphaDummy001) ∈
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ({(nb052AlphaDummy001)} : Finset Var) ∪
          ({(nb052AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb052AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb052AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy002))
              (synCun (Class.cv (nb052AlphaDummy000))
                (Class.cv (nb052AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy003 x y))
              (synCun (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0004 :
    (nb052AlphaDummy002) ∈
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ({(nb052AlphaDummy001)} : Finset Var) ∪
          ({(nb052AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb052AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb052AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy002))
              (synCun (Class.cv (nb052AlphaDummy000))
                (Class.cv (nb052AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0005 (x : Var) (y : Var) :
    (nb052AlphaDummy003 x y) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb052AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb052AlphaDummy003 x y))
              (synCun (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0006 :
    (nb052AlphaDummy000) ∈
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb052AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCun (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCun (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0008 :
    (nb052AlphaDummy000) ∈
      (((synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv ∪
        ((Class.cv (nb052AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0009 :
    (nb052AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
                (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCphi (Class.cv (nb052AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy006)
              (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0010 (x : Var) (y : Var) :
    x ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0011 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv)
        ((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0012 :
    (nb052AlphaDummy000) ∈
      (((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007))))))).fv ∪
        ((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0014 :
    (nb052AlphaDummy000) ∈
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0015 :
    (nb052AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb052AlphaDummy014)
              (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
                (Wff.classEq (Class.cv (nb052AlphaDummy014))
                  (synCphi (Class.cv (nb052AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy014)
              (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
                (Wff.classEq (Class.cv (nb052AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb052AlphaDummy016 x y)
              (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                  (synCphi (Class.cv (nb052AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy016 x y)
              (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0018 :
    (nb052AlphaDummy000) ∈
      (((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCphi (Class.cv (nb052AlphaDummy015))))))).fv ∪
        ((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCphi (Class.cv (nb052AlphaDummy015))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCphi (Class.cv (nb052AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCphi (Class.cv (nb052AlphaDummy017 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0020 :
    (nb052AlphaDummy015) ∈ (((Class.cv (nb052AlphaDummy015))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0021 (x : Var) (y : Var) :
    (nb052AlphaDummy017 x y) ∈ (((Class.cv (nb052AlphaDummy017 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0022 :
    (nb052AlphaDummy022) ∈
      (((Wff.classMem (Class.cv (nb052AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy022))).fv) :=
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

theorem nb052_support_mem_0023 (x : Var) (y : Var) :
    (nb052AlphaDummy024 x y) ∈
      (((Wff.classMem (Class.cv (nb052AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy024 x y))).fv) :=
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

theorem nb052_support_mem_0024 :
    (nb052AlphaDummy022) ∈
      (((Class.cv (nb052AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0025 (x : Var) (y : Var) :
    (nb052AlphaDummy024 x y) ∈
      (((Class.cv (nb052AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0026 :
    (nb052AlphaDummy029) ∈
      (((synCnin (Class.cv (nb052AlphaDummy029)) (Class.cv (nb052AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy029))
            (Class.cv (nb052AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0027 (x : Var) (y : Var) :
    (nb052AlphaDummy032 x y) ∈
      (((synCnin (Class.cv (nb052AlphaDummy032 x y))
            (Class.cv (nb052AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy032 x y))
            (Class.cv (nb052AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0028 :
    (nb052AlphaDummy029) ∈
      (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0029 (x : Var) (y : Var) :
    (nb052AlphaDummy032 x y) ∈
      (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0030 :
    (nb052AlphaDummy030) ∈
      (((synCnin (Class.cv (nb052AlphaDummy029)) (Class.cv (nb052AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy029))
            (Class.cv (nb052AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0031 (x : Var) (y : Var) :
    (nb052AlphaDummy033 x y) ∈
      (((synCnin (Class.cv (nb052AlphaDummy032 x y))
            (Class.cv (nb052AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy032 x y))
            (Class.cv (nb052AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0032 :
    (nb052AlphaDummy030) ∈
      (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0033 (x : Var) (y : Var) :
    (nb052AlphaDummy033 x y) ∈
      (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0034 :
    (nb052AlphaDummy029) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0035 (x : Var) (y : Var) :
    (nb052AlphaDummy032 x y) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0036 :
    (nb052AlphaDummy029) ∈
      (((Class.cv (nb052AlphaDummy029))).fv ∪ ((Class.cv (nb052AlphaDummy029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0037 (x : Var) (y : Var) :
    (nb052AlphaDummy032 x y) ∈
      (((Class.cv (nb052AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy032 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0038 :
    (nb052AlphaDummy030) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0039 (x : Var) (y : Var) :
    (nb052AlphaDummy033 x y) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0040 :
    (nb052AlphaDummy030) ∈
      (((Class.cv (nb052AlphaDummy030))).fv ∪ ((Class.cv (nb052AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0041 (x : Var) (y : Var) :
    (nb052AlphaDummy033 x y) ∈
      (((Class.cv (nb052AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0042 :
    (nb052AlphaDummy001) ∈
      (({(nb052AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb052AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCun (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0043 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCun (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0044 :
    (nb052AlphaDummy001) ∈
      (((synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv ∪
        ((Class.cv (nb052AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0045 :
    (nb052AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
                (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCphi (Class.cv (nb052AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy006)
              (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0046 (x : Var) (y : Var) :
    y ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv)
        ((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0048 :
    (nb052AlphaDummy001) ∈
      (((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007))))))).fv ∪
        ((Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
              (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCphi (Class.cv (nb052AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0049 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCphi (Class.cv (nb052AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0050 :
    (nb052AlphaDummy001) ∈
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0051 :
    (nb052AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb052AlphaDummy014)
              (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy000))
                (Wff.classEq (Class.cv (nb052AlphaDummy014))
                  (synCphi (Class.cv (nb052AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy014)
              (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
                (Wff.classEq (Class.cv (nb052AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb052AlphaDummy016 x y)
              (synWrex (nb052AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                  (synCphi (Class.cv (nb052AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy016 x y)
              (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0054 :
    (nb052AlphaDummy001) ∈
      (((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy014)
            (synWrex (nb052AlphaDummy015) (Class.cv (nb052AlphaDummy001))
              (Wff.classEq (Class.cv (nb052AlphaDummy014))
                (synCun (synCphi (Class.cv (nb052AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy016 x y)
            (synWrex (nb052AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb052AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0056 :
    (nb052AlphaDummy015) ∈
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0057 (x : Var) (y : Var) :
    (nb052AlphaDummy017 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0058 :
    (nb052AlphaDummy015) ∈
      (((synCphi (Class.cv (nb052AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy015)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0059 (x : Var) (y : Var) :
    (nb052AlphaDummy017 x y) ∈
      (((synCphi (Class.cv (nb052AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy017 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0060 :
    (nb052AlphaDummy007) ∈ (((Class.cv (nb052AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0061 (x : Var) (y : Var) :
    (nb052AlphaDummy009 x y) ∈ (((Class.cv (nb052AlphaDummy009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0062 :
    (nb052AlphaDummy050) ∈
      (((Wff.classMem (Class.cv (nb052AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy050))).fv) :=
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

theorem nb052_support_mem_0063 (x : Var) (y : Var) :
    (nb052AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb052AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb052AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb052AlphaDummy052 x y))).fv) :=
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

theorem nb052_support_mem_0064 :
    (nb052AlphaDummy050) ∈
      (((Class.cv (nb052AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0065 (x : Var) (y : Var) :
    (nb052AlphaDummy052 x y) ∈
      (((Class.cv (nb052AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0066 :
    (nb052AlphaDummy057) ∈
      (((synCnin (Class.cv (nb052AlphaDummy057)) (Class.cv (nb052AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy057))
            (Class.cv (nb052AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0067 (x : Var) (y : Var) :
    (nb052AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb052AlphaDummy060 x y))
            (Class.cv (nb052AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy060 x y))
            (Class.cv (nb052AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0068 :
    (nb052AlphaDummy057) ∈
      (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0069 (x : Var) (y : Var) :
    (nb052AlphaDummy060 x y) ∈
      (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0070 :
    (nb052AlphaDummy058) ∈
      (((synCnin (Class.cv (nb052AlphaDummy057)) (Class.cv (nb052AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy057))
            (Class.cv (nb052AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0071 (x : Var) (y : Var) :
    (nb052AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb052AlphaDummy060 x y))
            (Class.cv (nb052AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb052AlphaDummy060 x y))
            (Class.cv (nb052AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0072 :
    (nb052AlphaDummy058) ∈
      (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0073 (x : Var) (y : Var) :
    (nb052AlphaDummy061 x y) ∈
      (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0074 :
    (nb052AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0075 (x : Var) (y : Var) :
    (nb052AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0076 :
    (nb052AlphaDummy057) ∈
      (((Class.cv (nb052AlphaDummy057))).fv ∪ ((Class.cv (nb052AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0077 (x : Var) (y : Var) :
    (nb052AlphaDummy060 x y) ∈
      (((Class.cv (nb052AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0078 :
    (nb052AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0079 (x : Var) (y : Var) :
    (nb052AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0080 :
    (nb052AlphaDummy058) ∈
      (((Class.cv (nb052AlphaDummy058))).fv ∪ ((Class.cv (nb052AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0081 (x : Var) (y : Var) :
    (nb052AlphaDummy061 x y) ∈
      (((Class.cv (nb052AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb052AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0082 :
    (nb052AlphaDummy002) ∈
      (((synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))).fv ∪
        ((Class.cv (nb052AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0083 :
    (nb052AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb052AlphaDummy006) (synWrex (nb052AlphaDummy007)
                (synCop (Class.cv (nb052AlphaDummy000)) (Class.cv (nb052AlphaDummy001)))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCphi (Class.cv (nb052AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy006)
              (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
                (Wff.classEq (Class.cv (nb052AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0084 (x : Var) (y : Var) :
    (nb052AlphaDummy003 x y) ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb052AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0085 (x : Var) (y : Var) :
    (nb052AlphaDummy003 x y) ∈
      (((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := (nb052AlphaDummy003 x y)) (t := ((synCcompl
            (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv)
        ((synCcompl (Class.cab (nb052AlphaDummy008 x y)
              (synWrex (nb052AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                  (synCphi (Class.cv (nb052AlphaDummy009 x y)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0086 :
    (nb052AlphaDummy002) ∈
      (((Class.cab (nb052AlphaDummy006)
            (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy006)
            (synWrex (nb052AlphaDummy007) (Class.cv (nb052AlphaDummy002))
              (Wff.classEq (Class.cv (nb052AlphaDummy006))
                (synCun (synCphi (Class.cv (nb052AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
