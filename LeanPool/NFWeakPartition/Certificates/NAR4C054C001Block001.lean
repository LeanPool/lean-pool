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

/-! Certificates from `NAR4C054C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_000`. -/
@[expose]
noncomputable def nb054AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_001`. -/
@[expose]
noncomputable def nb054AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_002`. -/
@[expose]
noncomputable def nb054AlphaDummy002 : Var :=
  (freshVar (({(nb054AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
          ({(nb054AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCplc (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_003`. -/
@[expose]
noncomputable def nb054AlphaDummy003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCplc (Class.cv x) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_004`. -/
@[expose]
noncomputable def nb054AlphaDummy004 : Var :=
  (freshVar
    (({(nb054AlphaDummy000)} : Finset Var) ∪ ({(nb054AlphaDummy001)} : Finset Var) ∪
        ({(nb054AlphaDummy002)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv (nb054AlphaDummy000)) (synCvv))
            (Wff.classMem (Class.cv (nb054AlphaDummy001)) (synCvv)))
          (Wff.classEq (Class.cv (nb054AlphaDummy002))
            (synCplc (Class.cv (nb054AlphaDummy000))
              (Class.cv (nb054AlphaDummy001)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_005`. -/
@[expose]
noncomputable def nb054AlphaDummy005 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb054AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
          (Wff.classEq (Class.cv (nb054AlphaDummy003 x y))
            (synCplc (Class.cv x) (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_006`. -/
@[expose]
noncomputable def nb054AlphaDummy006 : Var :=
  (freshVar (((synCop (Class.cv (nb054AlphaDummy000))
          (Class.cv (nb054AlphaDummy001)))).fv ∪ ((Class.cv (nb054AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_007`. -/
@[expose]
noncomputable def nb054AlphaDummy007 : Var :=
  (freshVar (((synCop (Class.cv (nb054AlphaDummy000))
          (Class.cv (nb054AlphaDummy001)))).fv ∪ ((Class.cv (nb054AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_008`. -/
@[expose]
noncomputable def nb054AlphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb054AlphaDummy003 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_009`. -/
@[expose]
noncomputable def nb054AlphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb054AlphaDummy003 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_010`. -/
@[expose]
noncomputable def nb054AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb054AlphaDummy006)
            (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_011`. -/
@[expose]
noncomputable def nb054AlphaDummy011 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_012`. -/
@[expose]
noncomputable def nb054AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
            (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
            (Wff.classEq (Class.cv (nb054AlphaDummy006))
              (synCphi (Class.cv (nb054AlphaDummy007))))))).fv ∪
      ((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
            (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
            (Wff.classEq (Class.cv (nb054AlphaDummy006))
              (synCphi (Class.cv (nb054AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_013`. -/
@[expose]
noncomputable def nb054AlphaDummy013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb054AlphaDummy008 x y)
          (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
              (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv ∪
      ((Class.cab (nb054AlphaDummy008 x y)
          (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
              (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_014`. -/
@[expose]
noncomputable def nb054AlphaDummy014 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_015`. -/
@[expose]
noncomputable def nb054AlphaDummy015 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_016`. -/
@[expose]
noncomputable def nb054AlphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_017`. -/
@[expose]
noncomputable def nb054AlphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_018`. -/
@[expose]
noncomputable def nb054AlphaDummy018 : Var :=
  (freshVar (((synCcompl (Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCphi (Class.cv (nb054AlphaDummy015)))))))).fv ∪ ((synCcompl
          (Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_019`. -/
@[expose]
noncomputable def nb054AlphaDummy019 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCphi (Class.cv (nb054AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_020`. -/
@[expose]
noncomputable def nb054AlphaDummy020 : Var :=
  (freshVar (((Class.cab (nb054AlphaDummy014)
          (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
            (Wff.classEq (Class.cv (nb054AlphaDummy014))
              (synCphi (Class.cv (nb054AlphaDummy015))))))).fv ∪
      ((Class.cab (nb054AlphaDummy014)
          (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
            (Wff.classEq (Class.cv (nb054AlphaDummy014))
              (synCphi (Class.cv (nb054AlphaDummy015))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_021`. -/
@[expose]
noncomputable def nb054AlphaDummy021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb054AlphaDummy016 x y)
          (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
              (synCphi (Class.cv (nb054AlphaDummy017 x y))))))).fv ∪
      ((Class.cab (nb054AlphaDummy016 x y) (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
              (synCphi (Class.cv (nb054AlphaDummy017 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_022`. -/
@[expose]
noncomputable def nb054AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_023`. -/
@[expose]
noncomputable def nb054AlphaDummy023 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy015))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_024`. -/
@[expose]
noncomputable def nb054AlphaDummy024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_025`. -/
@[expose]
noncomputable def nb054AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy017 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_026`. -/
@[expose]
noncomputable def nb054AlphaDummy026 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb054AlphaDummy022)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb054AlphaDummy022)) (synC1c))).fv ∪
      ((Class.cv (nb054AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_027`. -/
@[expose]
noncomputable def nb054AlphaDummy027 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb054AlphaDummy024 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb054AlphaDummy024 x y)) (synC1c))).fv ∪
      ((Class.cv (nb054AlphaDummy024 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_028`. -/
@[expose]
noncomputable def nb054AlphaDummy028 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_029`. -/
@[expose]
noncomputable def nb054AlphaDummy029 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_030`. -/
@[expose]
noncomputable def nb054AlphaDummy030 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_031`. -/
@[expose]
noncomputable def nb054AlphaDummy031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_032`. -/
@[expose]
noncomputable def nb054AlphaDummy032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_033`. -/
@[expose]
noncomputable def nb054AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_034`. -/
@[expose]
noncomputable def nb054AlphaDummy034 : Var :=
  (freshVar (((synCnin (Class.cv (nb054AlphaDummy029))
          (Class.cv (nb054AlphaDummy030)))).fv ∪
      ((synCnin (Class.cv (nb054AlphaDummy029)) (Class.cv (nb054AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_035`. -/
@[expose]
noncomputable def nb054AlphaDummy035 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb054AlphaDummy032 x y))
          (Class.cv (nb054AlphaDummy033 x y)))).fv ∪
      ((synCnin (Class.cv (nb054AlphaDummy032 x y))
          (Class.cv (nb054AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_036`. -/
@[expose]
noncomputable def nb054AlphaDummy036 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_037`. -/
@[expose]
noncomputable def nb054AlphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_038`. -/
@[expose]
noncomputable def nb054AlphaDummy038 : Var :=
  (freshVar (((synCcompl (Class.cv (nb054AlphaDummy029)))).fv ∪
      ((synCcompl (Class.cv (nb054AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_039`. -/
@[expose]
noncomputable def nb054AlphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb054AlphaDummy032 x y)))).fv ∪
      ((synCcompl (Class.cv (nb054AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_040`. -/
@[expose]
noncomputable def nb054AlphaDummy040 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy029))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_041`. -/
@[expose]
noncomputable def nb054AlphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy032 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_042`. -/
@[expose]
noncomputable def nb054AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy030))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_043`. -/
@[expose]
noncomputable def nb054AlphaDummy043 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy033 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_044`. -/
@[expose]
noncomputable def nb054AlphaDummy044 : Var :=
  (freshVar (((Class.cab (nb054AlphaDummy014)
          (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
            (Wff.classEq (Class.cv (nb054AlphaDummy014))
              (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy014)
          (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
            (Wff.classEq (Class.cv (nb054AlphaDummy014))
              (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_045`. -/
@[expose]
noncomputable def nb054AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb054AlphaDummy016 x y)
          (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy016 x y)
          (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_046`. -/
@[expose]
noncomputable def nb054AlphaDummy046 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb054AlphaDummy015))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_047`. -/
@[expose]
noncomputable def nb054AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb054AlphaDummy017 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_048`. -/
@[expose]
noncomputable def nb054AlphaDummy048 : Var :=
  (freshVar (((synCphi (Class.cv (nb054AlphaDummy015)))).fv ∪
      ((synCphi (Class.cv (nb054AlphaDummy015)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_049`. -/
@[expose]
noncomputable def nb054AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
      ((synCphi (Class.cv (nb054AlphaDummy017 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_050`. -/
@[expose]
noncomputable def nb054AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_051`. -/
@[expose]
noncomputable def nb054AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_052`. -/
@[expose]
noncomputable def nb054AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy009 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_053`. -/
@[expose]
noncomputable def nb054AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy009 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_054`. -/
@[expose]
noncomputable def nb054AlphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb054AlphaDummy050)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb054AlphaDummy050)) (synC1c))).fv ∪
      ((Class.cv (nb054AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_055`. -/
@[expose]
noncomputable def nb054AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb054AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb054AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb054AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_056`. -/
@[expose]
noncomputable def nb054AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_057`. -/
@[expose]
noncomputable def nb054AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_058`. -/
@[expose]
noncomputable def nb054AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_059`. -/
@[expose]
noncomputable def nb054AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_060`. -/
@[expose]
noncomputable def nb054AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_061`. -/
@[expose]
noncomputable def nb054AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_062`. -/
@[expose]
noncomputable def nb054AlphaDummy062 : Var :=
  (freshVar (((synCnin (Class.cv (nb054AlphaDummy057))
          (Class.cv (nb054AlphaDummy058)))).fv ∪
      ((synCnin (Class.cv (nb054AlphaDummy057)) (Class.cv (nb054AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_063`. -/
@[expose]
noncomputable def nb054AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb054AlphaDummy060 x y))
          (Class.cv (nb054AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb054AlphaDummy060 x y))
          (Class.cv (nb054AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_064`. -/
@[expose]
noncomputable def nb054AlphaDummy064 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_065`. -/
@[expose]
noncomputable def nb054AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_066`. -/
@[expose]
noncomputable def nb054AlphaDummy066 : Var :=
  (freshVar (((synCcompl (Class.cv (nb054AlphaDummy057)))).fv ∪
      ((synCcompl (Class.cv (nb054AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_067`. -/
@[expose]
noncomputable def nb054AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb054AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb054AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_068`. -/
@[expose]
noncomputable def nb054AlphaDummy068 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_069`. -/
@[expose]
noncomputable def nb054AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_070`. -/
@[expose]
noncomputable def nb054AlphaDummy070 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy058))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_071`. -/
@[expose]
noncomputable def nb054AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_072`. -/
@[expose]
noncomputable def nb054AlphaDummy072 : Var :=
  (freshVar (((Class.cab (nb054AlphaDummy006)
          (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
            (Wff.classEq (Class.cv (nb054AlphaDummy006))
              (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy006)
          (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
            (Wff.classEq (Class.cv (nb054AlphaDummy006))
              (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_073`. -/
@[expose]
noncomputable def nb054AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb054AlphaDummy008 x y)
          (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy008 x y)
          (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_074`. -/
@[expose]
noncomputable def nb054AlphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb054AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_075`. -/
@[expose]
noncomputable def nb054AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb054AlphaDummy009 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_076`. -/
@[expose]
noncomputable def nb054AlphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv (nb054AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb054AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_077`. -/
@[expose]
noncomputable def nb054AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb054AlphaDummy009 x y)))).fv ∪
      ((synCphi (Class.cv (nb054AlphaDummy009 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_078`. -/
@[expose]
noncomputable def nb054AlphaDummy078 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_079`. -/
@[expose]
noncomputable def nb054AlphaDummy079 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_080`. -/
@[expose]
noncomputable def nb054AlphaDummy080 : Var :=
  (freshVar (((synCnin (Class.cv (nb054AlphaDummy015))
          (Class.cv (nb054AlphaDummy078)))).fv ∪
      ((synCnin (Class.cv (nb054AlphaDummy015)) (Class.cv (nb054AlphaDummy078)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_081`. -/
@[expose]
noncomputable def nb054AlphaDummy081 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb054AlphaDummy017 x y))
          (Class.cv (nb054AlphaDummy079 x y)))).fv ∪
      ((synCnin (Class.cv (nb054AlphaDummy017 x y))
          (Class.cv (nb054AlphaDummy079 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_082`. -/
@[expose]
noncomputable def nb054AlphaDummy082 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_083`. -/
@[expose]
noncomputable def nb054AlphaDummy083 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy079 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_084`. -/
@[expose]
noncomputable def nb054AlphaDummy084 : Var :=
  (freshVar (((synCcompl (Class.cv (nb054AlphaDummy015)))).fv ∪
      ((synCcompl (Class.cv (nb054AlphaDummy078)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_085`. -/
@[expose]
noncomputable def nb054AlphaDummy085 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
      ((synCcompl (Class.cv (nb054AlphaDummy079 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_086`. -/
@[expose]
noncomputable def nb054AlphaDummy086 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_087`. -/
@[expose]
noncomputable def nb054AlphaDummy087 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_088`. -/
@[expose]
noncomputable def nb054AlphaDummy088 : Var :=
  (freshVar
    (((Class.cv (nb054AlphaDummy078))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb054_alpha_dummy_089`. -/
@[expose]
noncomputable def nb054AlphaDummy089 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb054AlphaDummy079 x y))).fv ∪
      ((Class.cv (nb054AlphaDummy079 x y))).fv) 0)

theorem nb054_fresh_000 :
    (nb054AlphaDummy072) ∉
      (((Class.cab (nb054AlphaDummy006)
            (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy006)
            (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb054AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb054AlphaDummy006)
            (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy006)
            (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb054_fresh_001 :
    (nb054AlphaDummy012) ∉
      (((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007))))))).fv ∪
        ((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007))))))).fv) :=
  by
  simpa only [nb054AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007))))))).fv ∪
        ((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007))))))).fv)
      0

theorem nb054_fresh_002 (x : Var) (y : Var) :
    (nb054AlphaDummy073 x y) ∉
      (((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb054AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb054_fresh_003 (x : Var) (y : Var) :
    (nb054AlphaDummy013 x y) ∉
      (((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv) :=
  by
  simpa only [nb054AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv)
      0

theorem nb054_fresh_004 :
    (nb054AlphaDummy020) ∉
      (((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCphi (Class.cv (nb054AlphaDummy015))))))).fv ∪
        ((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCphi (Class.cv (nb054AlphaDummy015))))))).fv) :=
  by
  simpa only [nb054AlphaDummy020] using
    freshVar_not_mem
      (((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCphi (Class.cv (nb054AlphaDummy015))))))).fv ∪
        ((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCphi (Class.cv (nb054AlphaDummy015))))))).fv)
      0

theorem nb054_fresh_005 :
    (nb054AlphaDummy044) ∉
      (((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb054AlphaDummy044] using
    freshVar_not_mem
      (((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb054_fresh_006 (x : Var) (y : Var) :
    (nb054AlphaDummy021 x y) ∉
      (((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCphi (Class.cv (nb054AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCphi (Class.cv (nb054AlphaDummy017 x y))))))).fv) :=
  by
  simpa only [nb054AlphaDummy021] using
    freshVar_not_mem
      (((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCphi (Class.cv (nb054AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCphi (Class.cv (nb054AlphaDummy017 x y))))))).fv)
      0

theorem nb054_fresh_007 (x : Var) (y : Var) :
    (nb054AlphaDummy045 x y) ∉
      (((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb054AlphaDummy045] using
    freshVar_not_mem
      (((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb054_fresh_008 :
    (nb054AlphaDummy014) ∉
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv) :=
  by
  simpa only [nb054AlphaDummy014] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv)
      0

theorem nb054_fresh_009 :
    (nb054AlphaDummy015) ∉
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv) :=
  by
  simpa only [nb054AlphaDummy015] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv)
      1

theorem nb054_fresh_010 :
    (nb054AlphaDummy078) ∉
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv) :=
  by
  simpa only [nb054AlphaDummy078] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv)
      2

theorem nb054_distinct_011 : (nb054AlphaDummy014) ≠ (nb054AlphaDummy015) := by
  simpa only [nb054AlphaDummy014, nb054AlphaDummy015] using
    (freshVar_injective
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb054_distinct_012 : (nb054AlphaDummy014) ≠ (nb054AlphaDummy078) := by
  simpa only [nb054AlphaDummy014, nb054AlphaDummy078] using
    (freshVar_injective
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb054_distinct_013 : (nb054AlphaDummy015) ≠ (nb054AlphaDummy078) := by
  simpa only [nb054AlphaDummy015, nb054AlphaDummy078] using
    (freshVar_injective
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb054_fresh_014 :
    (nb054AlphaDummy050) ∉ (((Class.cv (nb054AlphaDummy007))).fv) := by
  simpa only [nb054AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy007))).fv) 0

theorem nb054_fresh_015 :
    (nb054AlphaDummy051) ∉ (((Class.cv (nb054AlphaDummy007))).fv) := by
  simpa only [nb054AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy007))).fv) 1

theorem nb054_distinct_016 : (nb054AlphaDummy050) ≠ (nb054AlphaDummy051) := by
  simpa only [nb054AlphaDummy050, nb054AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_017 (x : Var) (y : Var) :
    (nb054AlphaDummy052 x y) ∉ (((Class.cv (nb054AlphaDummy009 x y))).fv) := by
  simpa only [nb054AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy009 x y))).fv) 0

theorem nb054_fresh_018 (x : Var) (y : Var) :
    (nb054AlphaDummy053 x y) ∉ (((Class.cv (nb054AlphaDummy009 x y))).fv) := by
  simpa only [nb054AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy009 x y))).fv) 1

theorem nb054_distinct_019 (x : Var) (y : Var) :
    (nb054AlphaDummy052 x y) ≠ (nb054AlphaDummy053 x y) := by
  simpa only [nb054AlphaDummy052, nb054AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy009 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb054_fresh_020 :
    (nb054AlphaDummy022) ∉ (((Class.cv (nb054AlphaDummy015))).fv) := by
  simpa only [nb054AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy015))).fv) 0

theorem nb054_fresh_021 :
    (nb054AlphaDummy023) ∉ (((Class.cv (nb054AlphaDummy015))).fv) := by
  simpa only [nb054AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy015))).fv) 1

theorem nb054_distinct_022 : (nb054AlphaDummy022) ≠ (nb054AlphaDummy023) := by
  simpa only [nb054AlphaDummy022, nb054AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy015))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_023 :
    (nb054AlphaDummy086) ∉
      (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy015))).fv) :=
  by
  simpa only [nb054AlphaDummy086] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy015))).fv)
      0

theorem nb054_fresh_024 :
    (nb054AlphaDummy082) ∉
      (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv) :=
  by
  simpa only [nb054AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv)
      0

theorem nb054_fresh_025 (x : Var) (y : Var) :
    (nb054AlphaDummy024 x y) ∉ (((Class.cv (nb054AlphaDummy017 x y))).fv) := by
  simpa only [nb054AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy017 x y))).fv) 0

theorem nb054_fresh_026 (x : Var) (y : Var) :
    (nb054AlphaDummy025 x y) ∉ (((Class.cv (nb054AlphaDummy017 x y))).fv) := by
  simpa only [nb054AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy017 x y))).fv) 1

theorem nb054_distinct_027 (x : Var) (y : Var) :
    (nb054AlphaDummy024 x y) ≠ (nb054AlphaDummy025 x y) := by
  simpa only [nb054AlphaDummy024, nb054AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy017 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb054_fresh_028 (x : Var) (y : Var) :
    (nb054AlphaDummy087 x y) ∉
      (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy017 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy087] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy017 x y))).fv)
      0

theorem nb054_fresh_029 (x : Var) (y : Var) :
    (nb054AlphaDummy083 x y) ∉
      (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy079 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy083] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy079 x y))).fv)
      0

theorem nb054_fresh_030 :
    (nb054AlphaDummy028) ∉
      (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) 0

theorem nb054_fresh_031 :
    (nb054AlphaDummy029) ∉
      (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) 1

theorem nb054_fresh_032 :
    (nb054AlphaDummy030) ∉
      (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) 2

theorem nb054_distinct_033 : (nb054AlphaDummy028) ≠ (nb054AlphaDummy029) := by
  simpa only [nb054AlphaDummy028, nb054AlphaDummy029] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb054_distinct_034 : (nb054AlphaDummy028) ≠ (nb054AlphaDummy030) := by
  simpa only [nb054AlphaDummy028, nb054AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb054_distinct_035 : (nb054AlphaDummy029) ≠ (nb054AlphaDummy030) := by
  simpa only [nb054AlphaDummy029, nb054AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb054_fresh_036 (x : Var) (y : Var) :
    (nb054AlphaDummy031 x y) ∉
      (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb054_fresh_037 (x : Var) (y : Var) :
    (nb054AlphaDummy032 x y) ∉
      (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb054_fresh_038 (x : Var) (y : Var) :
    (nb054AlphaDummy033 x y) ∉
      (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb054_distinct_039 (x : Var) (y : Var) :
    (nb054AlphaDummy031 x y) ≠ (nb054AlphaDummy032 x y) := by
  simpa only [nb054AlphaDummy031, nb054AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb054_distinct_040 (x : Var) (y : Var) :
    (nb054AlphaDummy031 x y) ≠ (nb054AlphaDummy033 x y) := by
  simpa only [nb054AlphaDummy031, nb054AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb054_distinct_041 (x : Var) (y : Var) :
    (nb054AlphaDummy032 x y) ≠ (nb054AlphaDummy033 x y) := by
  simpa only [nb054AlphaDummy032, nb054AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb054_fresh_042 :
    (nb054AlphaDummy040) ∉
      (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy029))).fv) :=
  by
  simpa only [nb054AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy029))).fv)
      0

theorem nb054_fresh_043 :
    (nb054AlphaDummy036) ∉
      (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv) :=
  by
  simpa only [nb054AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv)
      0

theorem nb054_fresh_044 :
    (nb054AlphaDummy042) ∉
      (((Class.cv (nb054AlphaDummy030))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv) :=
  by
  simpa only [nb054AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy030))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv)
      0

theorem nb054_fresh_045 (x : Var) (y : Var) :
    (nb054AlphaDummy041 x y) ∉
      (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy032 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy032 x y))).fv)
      0

theorem nb054_fresh_046 (x : Var) (y : Var) :
    (nb054AlphaDummy037 x y) ∉
      (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy033 x y))).fv)
      0

theorem nb054_fresh_047 (x : Var) (y : Var) :
    (nb054AlphaDummy043 x y) ∉
      (((Class.cv (nb054AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy033 x y))).fv)
      0

theorem nb054_fresh_048 :
    (nb054AlphaDummy056) ∉
      (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) 0

theorem nb054_fresh_049 :
    (nb054AlphaDummy057) ∉
      (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) 1

theorem nb054_fresh_050 :
    (nb054AlphaDummy058) ∉
      (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) 2

theorem nb054_distinct_051 : (nb054AlphaDummy056) ≠ (nb054AlphaDummy057) := by
  simpa only [nb054AlphaDummy056, nb054AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb054_distinct_052 : (nb054AlphaDummy056) ≠ (nb054AlphaDummy058) := by
  simpa only [nb054AlphaDummy056, nb054AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb054_distinct_053 : (nb054AlphaDummy057) ≠ (nb054AlphaDummy058) := by
  simpa only [nb054AlphaDummy057, nb054AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb054_fresh_054 (x : Var) (y : Var) :
    (nb054AlphaDummy059 x y) ∉
      (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb054_fresh_055 (x : Var) (y : Var) :
    (nb054AlphaDummy060 x y) ∉
      (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb054_fresh_056 (x : Var) (y : Var) :
    (nb054AlphaDummy061 x y) ∉
      (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb054AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb054_distinct_057 (x : Var) (y : Var) :
    (nb054AlphaDummy059 x y) ≠ (nb054AlphaDummy060 x y) := by
  simpa only [nb054AlphaDummy059, nb054AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb054_distinct_058 (x : Var) (y : Var) :
    (nb054AlphaDummy059 x y) ≠ (nb054AlphaDummy061 x y) := by
  simpa only [nb054AlphaDummy059, nb054AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb054_distinct_059 (x : Var) (y : Var) :
    (nb054AlphaDummy060 x y) ≠ (nb054AlphaDummy061 x y) := by
  simpa only [nb054AlphaDummy060, nb054AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C054C001Part002`. -/


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

theorem nb054_fresh_060 :
    (nb054AlphaDummy068) ∉
      (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy057))).fv) :=
  by
  simpa only [nb054AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy057))).fv)
      0

theorem nb054_fresh_061 :
    (nb054AlphaDummy064) ∉
      (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv) :=
  by
  simpa only [nb054AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv)
      0

theorem nb054_fresh_062 :
    (nb054AlphaDummy070) ∉
      (((Class.cv (nb054AlphaDummy058))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv) :=
  by
  simpa only [nb054AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy058))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv)
      0

theorem nb054_fresh_063 (x : Var) (y : Var) :
    (nb054AlphaDummy069 x y) ∉
      (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy060 x y))).fv)
      0

theorem nb054_fresh_064 (x : Var) (y : Var) :
    (nb054AlphaDummy065 x y) ∉
      (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy061 x y))).fv)
      0

theorem nb054_fresh_065 (x : Var) (y : Var) :
    (nb054AlphaDummy071 x y) ∉
      (((Class.cv (nb054AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy061 x y))).fv)
      0

theorem nb054_fresh_066 :
    (nb054AlphaDummy088) ∉
      (((Class.cv (nb054AlphaDummy078))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv) :=
  by
  simpa only [nb054AlphaDummy088] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy078))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv)
      0

theorem nb054_fresh_067 (x : Var) (y : Var) :
    (nb054AlphaDummy089 x y) ∉
      (((Class.cv (nb054AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy079 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy089] using
    freshVar_not_mem
      (((Class.cv (nb054AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy079 x y))).fv)
      0

theorem nb054_fresh_068 (x : Var) (y : Var) :
    (nb054AlphaDummy016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb054AlphaDummy016] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb054_fresh_069 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb054AlphaDummy017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb054_fresh_070 (x : Var) (y : Var) :
    (nb054AlphaDummy079 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb054AlphaDummy079] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2

theorem nb054_distinct_071 (x : Var) (y : Var) :
    (nb054AlphaDummy016 x y) ≠ (nb054AlphaDummy017 x y) := by
  simpa only [nb054AlphaDummy016, nb054AlphaDummy017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb054_distinct_072 (x : Var) (y : Var) :
    (nb054AlphaDummy016 x y) ≠ (nb054AlphaDummy079 x y) := by
  simpa only [nb054AlphaDummy016, nb054AlphaDummy079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 2) (by decide))

theorem nb054_distinct_073 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ≠ (nb054AlphaDummy079 x y) := by
  simpa only [nb054AlphaDummy017, nb054AlphaDummy079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 1) (j := 2) (by decide))

theorem nb054_fresh_074 :
    (nb054AlphaDummy026) ∉
      (((Wff.classMem (Class.cv (nb054AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy022))).fv) :=
  by
  simpa only [nb054AlphaDummy026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb054AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy022))).fv)
      0

theorem nb054_fresh_075 (x : Var) (y : Var) :
    (nb054AlphaDummy027 x y) ∉
      (((Wff.classMem (Class.cv (nb054AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy024 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb054AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy024 x y))).fv)
      0

theorem nb054_fresh_076 :
    (nb054AlphaDummy054) ∉
      (((Wff.classMem (Class.cv (nb054AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy050))).fv) :=
  by
  simpa only [nb054AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb054AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy050))).fv)
      0

theorem nb054_fresh_077 (x : Var) (y : Var) :
    (nb054AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb054AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb054AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy052 x y))).fv)
      0

theorem nb054_fresh_078 :
    (nb054AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
                (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCphi (Class.cv (nb054AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy006)
              (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb054AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
                (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCphi (Class.cv (nb054AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy006)
              (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb054_fresh_079 (x : Var) (y : Var) :
    (nb054AlphaDummy011 x y) ∉
      (((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb054AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb054_fresh_080 :
    (nb054AlphaDummy018) ∉
      (((synCcompl (Class.cab (nb054AlphaDummy014)
              (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
                (Wff.classEq (Class.cv (nb054AlphaDummy014))
                  (synCphi (Class.cv (nb054AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy014)
              (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
                (Wff.classEq (Class.cv (nb054AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb054AlphaDummy018] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb054AlphaDummy014)
              (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
                (Wff.classEq (Class.cv (nb054AlphaDummy014))
                  (synCphi (Class.cv (nb054AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy014)
              (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
                (Wff.classEq (Class.cv (nb054AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb054_fresh_081 (x : Var) (y : Var) :
    (nb054AlphaDummy019 x y) ∉
      (((synCcompl (Class.cab (nb054AlphaDummy016 x y)
              (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                  (synCphi (Class.cv (nb054AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy016 x y)
              (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb054AlphaDummy019] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb054AlphaDummy016 x y)
              (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                  (synCphi (Class.cv (nb054AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy016 x y)
              (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb054_fresh_082 :
    (nb054AlphaDummy084) ∉
      (((synCcompl (Class.cv (nb054AlphaDummy015)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy078)))).fv) :=
  by
  simpa only [nb054AlphaDummy084] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb054AlphaDummy015)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy078)))).fv)
      0

theorem nb054_fresh_083 (x : Var) (y : Var) :
    (nb054AlphaDummy085 x y) ∉
      (((synCcompl (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy079 x y)))).fv) :=
  by
  simpa only [nb054AlphaDummy085] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy079 x y)))).fv)
      0

theorem nb054_fresh_084 :
    (nb054AlphaDummy038) ∉
      (((synCcompl (Class.cv (nb054AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy030)))).fv) :=
  by
  simpa only [nb054AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb054AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy030)))).fv)
      0

theorem nb054_fresh_085 (x : Var) (y : Var) :
    (nb054AlphaDummy039 x y) ∉
      (((synCcompl (Class.cv (nb054AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb054AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb054AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy033 x y)))).fv)
      0

theorem nb054_fresh_086 :
    (nb054AlphaDummy066) ∉
      (((synCcompl (Class.cv (nb054AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy058)))).fv) :=
  by
  simpa only [nb054AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb054AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy058)))).fv)
      0

theorem nb054_fresh_087 (x : Var) (y : Var) :
    (nb054AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb054AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb054AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb054AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy061 x y)))).fv)
      0

theorem nb054_fresh_088 :
    (nb054AlphaDummy074) ∉
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb054AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb054_fresh_089 (x : Var) (y : Var) :
    (nb054AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb054AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb054_fresh_090 :
    (nb054AlphaDummy046) ∉
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb054AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb054_fresh_091 (x : Var) (y : Var) :
    (nb054AlphaDummy047 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb054AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb054_fresh_092 :
    (nb054AlphaDummy080) ∉
      (((synCnin (Class.cv (nb054AlphaDummy015)) (Class.cv (nb054AlphaDummy078)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy015))
            (Class.cv (nb054AlphaDummy078)))).fv) :=
  by
  simpa only [nb054AlphaDummy080] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb054AlphaDummy015)) (Class.cv (nb054AlphaDummy078)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy015)) (Class.cv (nb054AlphaDummy078)))).fv)
      0

theorem nb054_fresh_093 (x : Var) (y : Var) :
    (nb054AlphaDummy081 x y) ∉
      (((synCnin (Class.cv (nb054AlphaDummy017 x y))
            (Class.cv (nb054AlphaDummy079 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy017 x y))
            (Class.cv (nb054AlphaDummy079 x y)))).fv) :=
  by
  simpa only [nb054AlphaDummy081] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb054AlphaDummy017 x y))
            (Class.cv (nb054AlphaDummy079 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy017 x y))
            (Class.cv (nb054AlphaDummy079 x y)))).fv)
      0

theorem nb054_fresh_094 :
    (nb054AlphaDummy034) ∉
      (((synCnin (Class.cv (nb054AlphaDummy029)) (Class.cv (nb054AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy029))
            (Class.cv (nb054AlphaDummy030)))).fv) :=
  by
  simpa only [nb054AlphaDummy034] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb054AlphaDummy029)) (Class.cv (nb054AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy029)) (Class.cv (nb054AlphaDummy030)))).fv)
      0

theorem nb054_fresh_095 (x : Var) (y : Var) :
    (nb054AlphaDummy035 x y) ∉
      (((synCnin (Class.cv (nb054AlphaDummy032 x y))
            (Class.cv (nb054AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy032 x y))
            (Class.cv (nb054AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb054AlphaDummy035] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb054AlphaDummy032 x y))
            (Class.cv (nb054AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy032 x y))
            (Class.cv (nb054AlphaDummy033 x y)))).fv)
      0

theorem nb054_fresh_096 :
    (nb054AlphaDummy062) ∉
      (((synCnin (Class.cv (nb054AlphaDummy057)) (Class.cv (nb054AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy057))
            (Class.cv (nb054AlphaDummy058)))).fv) :=
  by
  simpa only [nb054AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb054AlphaDummy057)) (Class.cv (nb054AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy057)) (Class.cv (nb054AlphaDummy058)))).fv)
      0

theorem nb054_fresh_097 (x : Var) (y : Var) :
    (nb054AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb054AlphaDummy060 x y))
            (Class.cv (nb054AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy060 x y))
            (Class.cv (nb054AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb054AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb054AlphaDummy060 x y))
            (Class.cv (nb054AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy060 x y))
            (Class.cv (nb054AlphaDummy061 x y)))).fv)
      0

theorem nb054_fresh_098 :
    (nb054AlphaDummy006) ∉
      (((synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv ∪
        ((Class.cv (nb054AlphaDummy002))).fv) :=
  by
  simpa only [nb054AlphaDummy006] using
    freshVar_not_mem
      (((synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv ∪
        ((Class.cv (nb054AlphaDummy002))).fv)
      0

theorem nb054_fresh_099 :
    (nb054AlphaDummy007) ∉
      (((synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv ∪
        ((Class.cv (nb054AlphaDummy002))).fv) :=
  by
  simpa only [nb054AlphaDummy007] using
    freshVar_not_mem
      (((synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv ∪
        ((Class.cv (nb054AlphaDummy002))).fv)
      1

theorem nb054_distinct_100 : (nb054AlphaDummy006) ≠ (nb054AlphaDummy007) := by
  simpa only [nb054AlphaDummy006, nb054AlphaDummy007] using
    (freshVar_injective (((synCop (Class.cv (nb054AlphaDummy000))
            (Class.cv (nb054AlphaDummy001)))).fv ∪ ((Class.cv (nb054AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb054_fresh_101 (x : Var) (y : Var) :
    (nb054AlphaDummy008 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb054AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy008] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054AlphaDummy003 x y))).fv)
      0

theorem nb054_fresh_102 (x : Var) (y : Var) :
    (nb054AlphaDummy009 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb054AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb054AlphaDummy009] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054AlphaDummy003 x y))).fv)
      1

theorem nb054_distinct_103 (x : Var) (y : Var) :
    (nb054AlphaDummy008 x y) ≠ (nb054AlphaDummy009 x y) := by
  simpa only [nb054AlphaDummy008, nb054AlphaDummy009] using
    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb054AlphaDummy003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_104 :
    (nb054AlphaDummy076) ∉
      (((synCphi (Class.cv (nb054AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy007)))).fv) :=
  by
  simpa only [nb054AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb054AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy007)))).fv)
      0

theorem nb054_fresh_105 (x : Var) (y : Var) :
    (nb054AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb054AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy009 x y)))).fv) :=
  by
  simpa only [nb054AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb054AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy009 x y)))).fv)
      0

theorem nb054_fresh_106 :
    (nb054AlphaDummy048) ∉
      (((synCphi (Class.cv (nb054AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy015)))).fv) :=
  by
  simpa only [nb054AlphaDummy048] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb054AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy015)))).fv)
      0

theorem nb054_fresh_107 (x : Var) (y : Var) :
    (nb054AlphaDummy049 x y) ∉
      (((synCphi (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy017 x y)))).fv) :=
  by
  simpa only [nb054AlphaDummy049] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy017 x y)))).fv)
      0

theorem nb054_fresh_108 :
    (nb054AlphaDummy002) ∉
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb054AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv (nb054AlphaDummy000))
            (Class.cv (nb054AlphaDummy001)))).fv) :=
  by
  simpa only [nb054AlphaDummy002] using
    freshVar_not_mem
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb054AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv)
      0

theorem nb054_fresh_109 :
    (nb054AlphaDummy004) ∉
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ({(nb054AlphaDummy001)} : Finset Var) ∪
          ({(nb054AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb054AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb054AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy002))
              (synCplc (Class.cv (nb054AlphaDummy000))
                (Class.cv (nb054AlphaDummy001)))))).fv) :=
  by
  simpa only [nb054AlphaDummy004] using
    freshVar_not_mem
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ({(nb054AlphaDummy001)} : Finset Var) ∪
          ({(nb054AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb054AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb054AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy002))
              (synCplc (Class.cv (nb054AlphaDummy000))
                (Class.cv (nb054AlphaDummy001)))))).fv)
      0

theorem nb054_fresh_110 (x : Var) (y : Var) :
    (nb054AlphaDummy003 x y) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb054AlphaDummy003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv x) (Class.cv y))).fv)
      0

theorem nb054_fresh_111 (x : Var) (y : Var) :
    (nb054AlphaDummy005 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb054AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy003 x y))
              (synCplc (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb054AlphaDummy005] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb054AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy003 x y))
              (synCplc (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb054_fresh_112 : (nb054AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb054AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb054_fresh_113 : (nb054AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb054AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb054_distinct_114 : (nb054AlphaDummy000) ≠ (nb054AlphaDummy001) := by
  simpa only [nb054AlphaDummy000, nb054AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb054_support_mem_0000 :
    (nb054AlphaDummy000) ∈
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ({(nb054AlphaDummy001)} : Finset Var) ∪
          ({(nb054AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb054AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb054AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy002))
              (synCplc (Class.cv (nb054AlphaDummy000))
                (Class.cv (nb054AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb054AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy003 x y))
              (synCplc (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0002 :
    (nb054AlphaDummy001) ∈
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ({(nb054AlphaDummy001)} : Finset Var) ∪
          ({(nb054AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb054AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb054AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy002))
              (synCplc (Class.cv (nb054AlphaDummy000))
                (Class.cv (nb054AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb054AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy003 x y))
              (synCplc (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0004 :
    (nb054AlphaDummy002) ∈
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ({(nb054AlphaDummy001)} : Finset Var) ∪
          ({(nb054AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb054AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb054AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy002))
              (synCplc (Class.cv (nb054AlphaDummy000))
                (Class.cv (nb054AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0005 (x : Var) (y : Var) :
    (nb054AlphaDummy003 x y) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb054AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb054AlphaDummy003 x y))
              (synCplc (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0006 :
    (nb054AlphaDummy000) ∈
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb054AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv (nb054AlphaDummy000))
            (Class.cv (nb054AlphaDummy001)))).fv) :=
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

theorem nb054_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv x) (Class.cv y))).fv) :=
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

theorem nb054_support_mem_0008 :
    (nb054AlphaDummy000) ∈
      (((synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv ∪
        ((Class.cv (nb054AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0009 :
    (nb054AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
                (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCphi (Class.cv (nb054AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy006)
              (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0010 (x : Var) (y : Var) :
    x ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb054AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0011 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv)
        ((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0012 :
    (nb054AlphaDummy000) ∈
      (((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007))))))).fv ∪
        ((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0014 :
    (nb054AlphaDummy000) ∈
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0015 :
    (nb054AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb054AlphaDummy014)
              (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
                (Wff.classEq (Class.cv (nb054AlphaDummy014))
                  (synCphi (Class.cv (nb054AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy014)
              (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
                (Wff.classEq (Class.cv (nb054AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb054AlphaDummy016 x y)
              (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                  (synCphi (Class.cv (nb054AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy016 x y)
              (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0018 :
    (nb054AlphaDummy000) ∈
      (((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCphi (Class.cv (nb054AlphaDummy015))))))).fv ∪
        ((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCphi (Class.cv (nb054AlphaDummy015))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCphi (Class.cv (nb054AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCphi (Class.cv (nb054AlphaDummy017 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0020 :
    (nb054AlphaDummy015) ∈ (((Class.cv (nb054AlphaDummy015))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0021 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ∈ (((Class.cv (nb054AlphaDummy017 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0022 :
    (nb054AlphaDummy022) ∈
      (((Wff.classMem (Class.cv (nb054AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy022))).fv) :=
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

theorem nb054_support_mem_0023 (x : Var) (y : Var) :
    (nb054AlphaDummy024 x y) ∈
      (((Wff.classMem (Class.cv (nb054AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy024 x y))).fv) :=
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

theorem nb054_support_mem_0024 :
    (nb054AlphaDummy022) ∈
      (((Class.cv (nb054AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0025 (x : Var) (y : Var) :
    (nb054AlphaDummy024 x y) ∈
      (((Class.cv (nb054AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0026 :
    (nb054AlphaDummy029) ∈
      (((synCnin (Class.cv (nb054AlphaDummy029)) (Class.cv (nb054AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy029))
            (Class.cv (nb054AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0027 (x : Var) (y : Var) :
    (nb054AlphaDummy032 x y) ∈
      (((synCnin (Class.cv (nb054AlphaDummy032 x y))
            (Class.cv (nb054AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy032 x y))
            (Class.cv (nb054AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0028 :
    (nb054AlphaDummy029) ∈
      (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0029 (x : Var) (y : Var) :
    (nb054AlphaDummy032 x y) ∈
      (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0030 :
    (nb054AlphaDummy030) ∈
      (((synCnin (Class.cv (nb054AlphaDummy029)) (Class.cv (nb054AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy029))
            (Class.cv (nb054AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0031 (x : Var) (y : Var) :
    (nb054AlphaDummy033 x y) ∈
      (((synCnin (Class.cv (nb054AlphaDummy032 x y))
            (Class.cv (nb054AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy032 x y))
            (Class.cv (nb054AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0032 :
    (nb054AlphaDummy030) ∈
      (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0033 (x : Var) (y : Var) :
    (nb054AlphaDummy033 x y) ∈
      (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0034 :
    (nb054AlphaDummy029) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0035 (x : Var) (y : Var) :
    (nb054AlphaDummy032 x y) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0036 :
    (nb054AlphaDummy029) ∈
      (((Class.cv (nb054AlphaDummy029))).fv ∪ ((Class.cv (nb054AlphaDummy029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0037 (x : Var) (y : Var) :
    (nb054AlphaDummy032 x y) ∈
      (((Class.cv (nb054AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy032 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0038 :
    (nb054AlphaDummy030) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0039 (x : Var) (y : Var) :
    (nb054AlphaDummy033 x y) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0040 :
    (nb054AlphaDummy030) ∈
      (((Class.cv (nb054AlphaDummy030))).fv ∪ ((Class.cv (nb054AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0041 (x : Var) (y : Var) :
    (nb054AlphaDummy033 x y) ∈
      (((Class.cv (nb054AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0042 :
    (nb054AlphaDummy001) ∈
      (({(nb054AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb054AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv (nb054AlphaDummy000))
            (Class.cv (nb054AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0043 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCplc (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0044 :
    (nb054AlphaDummy001) ∈
      (((synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv ∪
        ((Class.cv (nb054AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0045 :
    (nb054AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
                (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCphi (Class.cv (nb054AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy006)
              (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0046 (x : Var) (y : Var) :
    y ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb054AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv)
        ((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0048 :
    (nb054AlphaDummy001) ∈
      (((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007))))))).fv ∪
        ((Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
              (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCphi (Class.cv (nb054AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0049 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCphi (Class.cv (nb054AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0050 :
    (nb054AlphaDummy001) ∈
      (((Class.cv (nb054AlphaDummy000))).fv ∪ ((Class.cv (nb054AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0051 :
    (nb054AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb054AlphaDummy014)
              (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy000))
                (Wff.classEq (Class.cv (nb054AlphaDummy014))
                  (synCphi (Class.cv (nb054AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy014)
              (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
                (Wff.classEq (Class.cv (nb054AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb054AlphaDummy016 x y)
              (synWrex (nb054AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                  (synCphi (Class.cv (nb054AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy016 x y)
              (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0054 :
    (nb054AlphaDummy001) ∈
      (((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy014)
            (synWrex (nb054AlphaDummy015) (Class.cv (nb054AlphaDummy001))
              (Wff.classEq (Class.cv (nb054AlphaDummy014))
                (synCun (synCphi (Class.cv (nb054AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy016 x y)
            (synWrex (nb054AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb054AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0056 :
    (nb054AlphaDummy015) ∈
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0057 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0058 :
    (nb054AlphaDummy015) ∈
      (((synCphi (Class.cv (nb054AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy015)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0059 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ∈
      (((synCphi (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy017 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0060 :
    (nb054AlphaDummy007) ∈ (((Class.cv (nb054AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0061 (x : Var) (y : Var) :
    (nb054AlphaDummy009 x y) ∈ (((Class.cv (nb054AlphaDummy009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0062 :
    (nb054AlphaDummy050) ∈
      (((Wff.classMem (Class.cv (nb054AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy050))).fv) :=
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

theorem nb054_support_mem_0063 (x : Var) (y : Var) :
    (nb054AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb054AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb054AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb054AlphaDummy052 x y))).fv) :=
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

theorem nb054_support_mem_0064 :
    (nb054AlphaDummy050) ∈
      (((Class.cv (nb054AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0065 (x : Var) (y : Var) :
    (nb054AlphaDummy052 x y) ∈
      (((Class.cv (nb054AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0066 :
    (nb054AlphaDummy057) ∈
      (((synCnin (Class.cv (nb054AlphaDummy057)) (Class.cv (nb054AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy057))
            (Class.cv (nb054AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0067 (x : Var) (y : Var) :
    (nb054AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb054AlphaDummy060 x y))
            (Class.cv (nb054AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy060 x y))
            (Class.cv (nb054AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0068 :
    (nb054AlphaDummy057) ∈
      (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0069 (x : Var) (y : Var) :
    (nb054AlphaDummy060 x y) ∈
      (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0070 :
    (nb054AlphaDummy058) ∈
      (((synCnin (Class.cv (nb054AlphaDummy057)) (Class.cv (nb054AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy057))
            (Class.cv (nb054AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0071 (x : Var) (y : Var) :
    (nb054AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb054AlphaDummy060 x y))
            (Class.cv (nb054AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy060 x y))
            (Class.cv (nb054AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0072 :
    (nb054AlphaDummy058) ∈
      (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0073 (x : Var) (y : Var) :
    (nb054AlphaDummy061 x y) ∈
      (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0074 :
    (nb054AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0075 (x : Var) (y : Var) :
    (nb054AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0076 :
    (nb054AlphaDummy057) ∈
      (((Class.cv (nb054AlphaDummy057))).fv ∪ ((Class.cv (nb054AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0077 (x : Var) (y : Var) :
    (nb054AlphaDummy060 x y) ∈
      (((Class.cv (nb054AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0078 :
    (nb054AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
