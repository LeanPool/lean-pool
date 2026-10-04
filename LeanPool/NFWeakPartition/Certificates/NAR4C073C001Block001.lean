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

/-! Certificates from `NAR4C073C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_000`. -/
@[expose]
noncomputable def nb073AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_001`. -/
@[expose]
noncomputable def nb073AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_002`. -/
@[expose]
noncomputable def nb073AlphaDummy002 : Var :=
  (freshVar (({(nb073AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
          ({(nb073AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCxp (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_003`. -/
@[expose]
noncomputable def nb073AlphaDummy003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCxp (Class.cv x) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_004`. -/
@[expose]
noncomputable def nb073AlphaDummy004 : Var :=
  (freshVar
    (({(nb073AlphaDummy000)} : Finset Var) ∪ ({(nb073AlphaDummy001)} : Finset Var) ∪
        ({(nb073AlphaDummy002)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv (nb073AlphaDummy000)) (synCvv))
            (Wff.classMem (Class.cv (nb073AlphaDummy001)) (synCvv)))
          (Wff.classEq (Class.cv (nb073AlphaDummy002))
            (synCxp (Class.cv (nb073AlphaDummy000))
              (Class.cv (nb073AlphaDummy001)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_005`. -/
@[expose]
noncomputable def nb073AlphaDummy005 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb073AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
          (Wff.classEq (Class.cv (nb073AlphaDummy003 x y))
            (synCxp (Class.cv x) (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_006`. -/
@[expose]
noncomputable def nb073AlphaDummy006 : Var :=
  (freshVar (((synCop (Class.cv (nb073AlphaDummy000))
          (Class.cv (nb073AlphaDummy001)))).fv ∪ ((Class.cv (nb073AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_007`. -/
@[expose]
noncomputable def nb073AlphaDummy007 : Var :=
  (freshVar (((synCop (Class.cv (nb073AlphaDummy000))
          (Class.cv (nb073AlphaDummy001)))).fv ∪ ((Class.cv (nb073AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_008`. -/
@[expose]
noncomputable def nb073AlphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb073AlphaDummy003 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_009`. -/
@[expose]
noncomputable def nb073AlphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb073AlphaDummy003 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_010`. -/
@[expose]
noncomputable def nb073AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb073AlphaDummy006)
            (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_011`. -/
@[expose]
noncomputable def nb073AlphaDummy011 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_012`. -/
@[expose]
noncomputable def nb073AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
            (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
            (Wff.classEq (Class.cv (nb073AlphaDummy006))
              (synCphi (Class.cv (nb073AlphaDummy007))))))).fv ∪
      ((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
            (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
            (Wff.classEq (Class.cv (nb073AlphaDummy006))
              (synCphi (Class.cv (nb073AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_013`. -/
@[expose]
noncomputable def nb073AlphaDummy013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy008 x y)
          (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
              (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv ∪
      ((Class.cab (nb073AlphaDummy008 x y)
          (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
              (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_014`. -/
@[expose]
noncomputable def nb073AlphaDummy014 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_015`. -/
@[expose]
noncomputable def nb073AlphaDummy015 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_016`. -/
@[expose]
noncomputable def nb073AlphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_017`. -/
@[expose]
noncomputable def nb073AlphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_018`. -/
@[expose]
noncomputable def nb073AlphaDummy018 : Var :=
  (freshVar (((synCcompl (Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCphi (Class.cv (nb073AlphaDummy015)))))))).fv ∪ ((synCcompl
          (Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_019`. -/
@[expose]
noncomputable def nb073AlphaDummy019 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCphi (Class.cv (nb073AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_020`. -/
@[expose]
noncomputable def nb073AlphaDummy020 : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy014)
          (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
            (Wff.classEq (Class.cv (nb073AlphaDummy014))
              (synCphi (Class.cv (nb073AlphaDummy015))))))).fv ∪
      ((Class.cab (nb073AlphaDummy014)
          (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
            (Wff.classEq (Class.cv (nb073AlphaDummy014))
              (synCphi (Class.cv (nb073AlphaDummy015))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_021`. -/
@[expose]
noncomputable def nb073AlphaDummy021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy016 x y)
          (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
              (synCphi (Class.cv (nb073AlphaDummy017 x y))))))).fv ∪
      ((Class.cab (nb073AlphaDummy016 x y) (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
              (synCphi (Class.cv (nb073AlphaDummy017 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_022`. -/
@[expose]
noncomputable def nb073AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_023`. -/
@[expose]
noncomputable def nb073AlphaDummy023 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy015))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_024`. -/
@[expose]
noncomputable def nb073AlphaDummy024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_025`. -/
@[expose]
noncomputable def nb073AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy017 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_026`. -/
@[expose]
noncomputable def nb073AlphaDummy026 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073AlphaDummy022)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb073AlphaDummy022)) (synC1c))).fv ∪
      ((Class.cv (nb073AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_027`. -/
@[expose]
noncomputable def nb073AlphaDummy027 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073AlphaDummy024 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb073AlphaDummy024 x y)) (synC1c))).fv ∪
      ((Class.cv (nb073AlphaDummy024 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_028`. -/
@[expose]
noncomputable def nb073AlphaDummy028 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_029`. -/
@[expose]
noncomputable def nb073AlphaDummy029 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_030`. -/
@[expose]
noncomputable def nb073AlphaDummy030 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_031`. -/
@[expose]
noncomputable def nb073AlphaDummy031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_032`. -/
@[expose]
noncomputable def nb073AlphaDummy032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_033`. -/
@[expose]
noncomputable def nb073AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_034`. -/
@[expose]
noncomputable def nb073AlphaDummy034 : Var :=
  (freshVar (((synCnin (Class.cv (nb073AlphaDummy029))
          (Class.cv (nb073AlphaDummy030)))).fv ∪
      ((synCnin (Class.cv (nb073AlphaDummy029)) (Class.cv (nb073AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_035`. -/
@[expose]
noncomputable def nb073AlphaDummy035 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb073AlphaDummy032 x y))
          (Class.cv (nb073AlphaDummy033 x y)))).fv ∪
      ((synCnin (Class.cv (nb073AlphaDummy032 x y))
          (Class.cv (nb073AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_036`. -/
@[expose]
noncomputable def nb073AlphaDummy036 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_037`. -/
@[expose]
noncomputable def nb073AlphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_038`. -/
@[expose]
noncomputable def nb073AlphaDummy038 : Var :=
  (freshVar (((synCcompl (Class.cv (nb073AlphaDummy029)))).fv ∪
      ((synCcompl (Class.cv (nb073AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_039`. -/
@[expose]
noncomputable def nb073AlphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb073AlphaDummy032 x y)))).fv ∪
      ((synCcompl (Class.cv (nb073AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_040`. -/
@[expose]
noncomputable def nb073AlphaDummy040 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy029))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_041`. -/
@[expose]
noncomputable def nb073AlphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy032 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_042`. -/
@[expose]
noncomputable def nb073AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy030))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_043`. -/
@[expose]
noncomputable def nb073AlphaDummy043 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy033 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_044`. -/
@[expose]
noncomputable def nb073AlphaDummy044 : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy014)
          (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
            (Wff.classEq (Class.cv (nb073AlphaDummy014))
              (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy014)
          (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
            (Wff.classEq (Class.cv (nb073AlphaDummy014))
              (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_045`. -/
@[expose]
noncomputable def nb073AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy016 x y)
          (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy016 x y)
          (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_046`. -/
@[expose]
noncomputable def nb073AlphaDummy046 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb073AlphaDummy015))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_047`. -/
@[expose]
noncomputable def nb073AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb073AlphaDummy017 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_048`. -/
@[expose]
noncomputable def nb073AlphaDummy048 : Var :=
  (freshVar (((synCphi (Class.cv (nb073AlphaDummy015)))).fv ∪
      ((synCphi (Class.cv (nb073AlphaDummy015)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_049`. -/
@[expose]
noncomputable def nb073AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb073AlphaDummy017 x y)))).fv ∪
      ((synCphi (Class.cv (nb073AlphaDummy017 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_050`. -/
@[expose]
noncomputable def nb073AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_051`. -/
@[expose]
noncomputable def nb073AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_052`. -/
@[expose]
noncomputable def nb073AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy009 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_053`. -/
@[expose]
noncomputable def nb073AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy009 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_054`. -/
@[expose]
noncomputable def nb073AlphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073AlphaDummy050)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb073AlphaDummy050)) (synC1c))).fv ∪
      ((Class.cv (nb073AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_055`. -/
@[expose]
noncomputable def nb073AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb073AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb073AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_056`. -/
@[expose]
noncomputable def nb073AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_057`. -/
@[expose]
noncomputable def nb073AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_058`. -/
@[expose]
noncomputable def nb073AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_059`. -/
@[expose]
noncomputable def nb073AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_060`. -/
@[expose]
noncomputable def nb073AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_061`. -/
@[expose]
noncomputable def nb073AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_062`. -/
@[expose]
noncomputable def nb073AlphaDummy062 : Var :=
  (freshVar (((synCnin (Class.cv (nb073AlphaDummy057))
          (Class.cv (nb073AlphaDummy058)))).fv ∪
      ((synCnin (Class.cv (nb073AlphaDummy057)) (Class.cv (nb073AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_063`. -/
@[expose]
noncomputable def nb073AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb073AlphaDummy060 x y))
          (Class.cv (nb073AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb073AlphaDummy060 x y))
          (Class.cv (nb073AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_064`. -/
@[expose]
noncomputable def nb073AlphaDummy064 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_065`. -/
@[expose]
noncomputable def nb073AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_066`. -/
@[expose]
noncomputable def nb073AlphaDummy066 : Var :=
  (freshVar (((synCcompl (Class.cv (nb073AlphaDummy057)))).fv ∪
      ((synCcompl (Class.cv (nb073AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_067`. -/
@[expose]
noncomputable def nb073AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb073AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb073AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_068`. -/
@[expose]
noncomputable def nb073AlphaDummy068 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_069`. -/
@[expose]
noncomputable def nb073AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_070`. -/
@[expose]
noncomputable def nb073AlphaDummy070 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy058))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_071`. -/
@[expose]
noncomputable def nb073AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_072`. -/
@[expose]
noncomputable def nb073AlphaDummy072 : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy006)
          (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
            (Wff.classEq (Class.cv (nb073AlphaDummy006))
              (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy006)
          (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
            (Wff.classEq (Class.cv (nb073AlphaDummy006))
              (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_073`. -/
@[expose]
noncomputable def nb073AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy008 x y)
          (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy008 x y)
          (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_074`. -/
@[expose]
noncomputable def nb073AlphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb073AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_075`. -/
@[expose]
noncomputable def nb073AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb073AlphaDummy009 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_076`. -/
@[expose]
noncomputable def nb073AlphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv (nb073AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb073AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_077`. -/
@[expose]
noncomputable def nb073AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb073AlphaDummy009 x y)))).fv ∪
      ((synCphi (Class.cv (nb073AlphaDummy009 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_078`. -/
@[expose]
noncomputable def nb073AlphaDummy078 : Var :=
  (freshVar
    (({(nb073AlphaDummy014)} : Finset Var) ∪ ({(nb073AlphaDummy015)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy014))
            (Class.cv (nb073AlphaDummy000))) (Wff.classMem (Class.cv (nb073AlphaDummy015))
            (Class.cv (nb073AlphaDummy001))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_079`. -/
@[expose]
noncomputable def nb073AlphaDummy079 (x : Var) (y : Var) : Var :=
  (freshVar (({(nb073AlphaDummy016 x y)} : Finset Var) ∪
        ({(nb073AlphaDummy017 x y)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy016 x y)) (Class.cv x))
          (Wff.classMem (Class.cv (nb073AlphaDummy017 x y)) (Class.cv y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_080`. -/
@[expose]
noncomputable def nb073AlphaDummy080 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_081`. -/
@[expose]
noncomputable def nb073AlphaDummy081 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_082`. -/
@[expose]
noncomputable def nb073AlphaDummy082 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_083`. -/
@[expose]
noncomputable def nb073AlphaDummy083 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy017 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_084`. -/
@[expose]
noncomputable def nb073AlphaDummy084 : Var :=
  (freshVar (((synCcompl (Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCphi (Class.cv (nb073AlphaDummy081)))))))).fv ∪ ((synCcompl
          (Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_085`. -/
@[expose]
noncomputable def nb073AlphaDummy085 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCphi (Class.cv (nb073AlphaDummy083 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_086`. -/
@[expose]
noncomputable def nb073AlphaDummy086 : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy080)
          (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
            (Wff.classEq (Class.cv (nb073AlphaDummy080))
              (synCphi (Class.cv (nb073AlphaDummy081))))))).fv ∪
      ((Class.cab (nb073AlphaDummy080)
          (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
            (Wff.classEq (Class.cv (nb073AlphaDummy080))
              (synCphi (Class.cv (nb073AlphaDummy081))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_087`. -/
@[expose]
noncomputable def nb073AlphaDummy087 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy082 x y)
          (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
            (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
              (synCphi (Class.cv (nb073AlphaDummy083 x y))))))).fv ∪
      ((Class.cab (nb073AlphaDummy082 x y)
          (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
            (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
              (synCphi (Class.cv (nb073AlphaDummy083 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_088`. -/
@[expose]
noncomputable def nb073AlphaDummy088 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy081))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_089`. -/
@[expose]
noncomputable def nb073AlphaDummy089 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy081))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_090`. -/
@[expose]
noncomputable def nb073AlphaDummy090 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy083 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_091`. -/
@[expose]
noncomputable def nb073AlphaDummy091 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy083 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_092`. -/
@[expose]
noncomputable def nb073AlphaDummy092 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073AlphaDummy088)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb073AlphaDummy088)) (synC1c))).fv ∪
      ((Class.cv (nb073AlphaDummy088))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_093`. -/
@[expose]
noncomputable def nb073AlphaDummy093 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb073AlphaDummy090 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb073AlphaDummy090 x y)) (synC1c))).fv ∪
      ((Class.cv (nb073AlphaDummy090 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_094`. -/
@[expose]
noncomputable def nb073AlphaDummy094 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_095`. -/
@[expose]
noncomputable def nb073AlphaDummy095 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_096`. -/
@[expose]
noncomputable def nb073AlphaDummy096 : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_097`. -/
@[expose]
noncomputable def nb073AlphaDummy097 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_098`. -/
@[expose]
noncomputable def nb073AlphaDummy098 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_099`. -/
@[expose]
noncomputable def nb073AlphaDummy099 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_100`. -/
@[expose]
noncomputable def nb073AlphaDummy100 : Var :=
  (freshVar (((synCnin (Class.cv (nb073AlphaDummy095))
          (Class.cv (nb073AlphaDummy096)))).fv ∪
      ((synCnin (Class.cv (nb073AlphaDummy095)) (Class.cv (nb073AlphaDummy096)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_101`. -/
@[expose]
noncomputable def nb073AlphaDummy101 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb073AlphaDummy098 x y))
          (Class.cv (nb073AlphaDummy099 x y)))).fv ∪
      ((synCnin (Class.cv (nb073AlphaDummy098 x y))
          (Class.cv (nb073AlphaDummy099 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_102`. -/
@[expose]
noncomputable def nb073AlphaDummy102 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_103`. -/
@[expose]
noncomputable def nb073AlphaDummy103 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy099 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_104`. -/
@[expose]
noncomputable def nb073AlphaDummy104 : Var :=
  (freshVar (((synCcompl (Class.cv (nb073AlphaDummy095)))).fv ∪
      ((synCcompl (Class.cv (nb073AlphaDummy096)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_105`. -/
@[expose]
noncomputable def nb073AlphaDummy105 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb073AlphaDummy098 x y)))).fv ∪
      ((synCcompl (Class.cv (nb073AlphaDummy099 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_106`. -/
@[expose]
noncomputable def nb073AlphaDummy106 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy095))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_107`. -/
@[expose]
noncomputable def nb073AlphaDummy107 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy098 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_108`. -/
@[expose]
noncomputable def nb073AlphaDummy108 : Var :=
  (freshVar
    (((Class.cv (nb073AlphaDummy096))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_109`. -/
@[expose]
noncomputable def nb073AlphaDummy109 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb073AlphaDummy099 x y))).fv ∪
      ((Class.cv (nb073AlphaDummy099 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_110`. -/
@[expose]
noncomputable def nb073AlphaDummy110 : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy080)
          (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
            (Wff.classEq (Class.cv (nb073AlphaDummy080))
              (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy080)
          (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
            (Wff.classEq (Class.cv (nb073AlphaDummy080))
              (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_111`. -/
@[expose]
noncomputable def nb073AlphaDummy111 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb073AlphaDummy082 x y)
          (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
            (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
              (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy082 x y)
          (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
            (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
              (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_112`. -/
@[expose]
noncomputable def nb073AlphaDummy112 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb073AlphaDummy081))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_113`. -/
@[expose]
noncomputable def nb073AlphaDummy113 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb073AlphaDummy083 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_114`. -/
@[expose]
noncomputable def nb073AlphaDummy114 : Var :=
  (freshVar (((synCphi (Class.cv (nb073AlphaDummy081)))).fv ∪
      ((synCphi (Class.cv (nb073AlphaDummy081)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb073_alpha_dummy_115`. -/
@[expose]
noncomputable def nb073AlphaDummy115 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb073AlphaDummy083 x y)))).fv ∪
      ((synCphi (Class.cv (nb073AlphaDummy083 x y)))).fv) 0)

theorem nb073_fresh_000 :
    (nb073AlphaDummy072) ∉
      (((Class.cab (nb073AlphaDummy006)
            (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy006)
            (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb073AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy006)
            (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy006)
            (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb073_fresh_001 :
    (nb073AlphaDummy012) ∉
      (((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))).fv ∪
        ((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))).fv) :=
  by
  simpa only [nb073AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))).fv ∪
        ((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))).fv)
      0

theorem nb073_fresh_002 (x : Var) (y : Var) :
    (nb073AlphaDummy073 x y) ∉
      (((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb073AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb073_fresh_003 (x : Var) (y : Var) :
    (nb073AlphaDummy013 x y) ∉
      (((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv) :=
  by
  simpa only [nb073AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv)
      0

theorem nb073_fresh_004 :
    (nb073AlphaDummy020) ∉
      (((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCphi (Class.cv (nb073AlphaDummy015))))))).fv ∪
        ((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCphi (Class.cv (nb073AlphaDummy015))))))).fv) :=
  by
  simpa only [nb073AlphaDummy020] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCphi (Class.cv (nb073AlphaDummy015))))))).fv ∪
        ((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCphi (Class.cv (nb073AlphaDummy015))))))).fv)
      0

theorem nb073_fresh_005 :
    (nb073AlphaDummy044) ∉
      (((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb073AlphaDummy044] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb073_fresh_006 (x : Var) (y : Var) :
    (nb073AlphaDummy021 x y) ∉
      (((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCphi (Class.cv (nb073AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCphi (Class.cv (nb073AlphaDummy017 x y))))))).fv) :=
  by
  simpa only [nb073AlphaDummy021] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCphi (Class.cv (nb073AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCphi (Class.cv (nb073AlphaDummy017 x y))))))).fv)
      0

theorem nb073_fresh_007 (x : Var) (y : Var) :
    (nb073AlphaDummy045 x y) ∉
      (((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb073AlphaDummy045] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb073_fresh_008 :
    (nb073AlphaDummy086) ∉
      (((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCphi (Class.cv (nb073AlphaDummy081))))))).fv ∪
        ((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCphi (Class.cv (nb073AlphaDummy081))))))).fv) :=
  by
  simpa only [nb073AlphaDummy086] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCphi (Class.cv (nb073AlphaDummy081))))))).fv ∪
        ((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCphi (Class.cv (nb073AlphaDummy081))))))).fv)
      0

theorem nb073_fresh_009 :
    (nb073AlphaDummy110) ∉
      (((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb073AlphaDummy110] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb073_fresh_010 (x : Var) (y : Var) :
    (nb073AlphaDummy087 x y) ∉
      (((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCphi (Class.cv (nb073AlphaDummy083 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCphi (Class.cv (nb073AlphaDummy083 x y))))))).fv) :=
  by
  simpa only [nb073AlphaDummy087] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCphi (Class.cv (nb073AlphaDummy083 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCphi (Class.cv (nb073AlphaDummy083 x y))))))).fv)
      0

theorem nb073_fresh_011 (x : Var) (y : Var) :
    (nb073AlphaDummy111 x y) ∉
      (((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb073AlphaDummy111] using
    freshVar_not_mem
      (((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb073_fresh_012 :
    (nb073AlphaDummy014) ∉
      (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv) :=
  by
  simpa only [nb073AlphaDummy014] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv)
      0

theorem nb073_fresh_013 :
    (nb073AlphaDummy015) ∉
      (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv) :=
  by
  simpa only [nb073AlphaDummy015] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv)
      1

theorem nb073_distinct_014 : (nb073AlphaDummy014) ≠ (nb073AlphaDummy015) := by
  simpa only [nb073AlphaDummy014, nb073AlphaDummy015] using
    (freshVar_injective
      (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_fresh_015 :
    (nb073AlphaDummy050) ∉ (((Class.cv (nb073AlphaDummy007))).fv) := by
  simpa only [nb073AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy007))).fv) 0

theorem nb073_fresh_016 :
    (nb073AlphaDummy051) ∉ (((Class.cv (nb073AlphaDummy007))).fv) := by
  simpa only [nb073AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy007))).fv) 1

theorem nb073_distinct_017 : (nb073AlphaDummy050) ≠ (nb073AlphaDummy051) := by
  simpa only [nb073AlphaDummy050, nb073AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_018 (x : Var) (y : Var) :
    (nb073AlphaDummy052 x y) ∉ (((Class.cv (nb073AlphaDummy009 x y))).fv) := by
  simpa only [nb073AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy009 x y))).fv) 0

theorem nb073_fresh_019 (x : Var) (y : Var) :
    (nb073AlphaDummy053 x y) ∉ (((Class.cv (nb073AlphaDummy009 x y))).fv) := by
  simpa only [nb073AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy009 x y))).fv) 1

theorem nb073_distinct_020 (x : Var) (y : Var) :
    (nb073AlphaDummy052 x y) ≠ (nb073AlphaDummy053 x y) := by
  simpa only [nb073AlphaDummy052, nb073AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy009 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb073_fresh_021 :
    (nb073AlphaDummy080) ∉
      (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv) :=
  by
  simpa only [nb073AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv)
      0

theorem nb073_fresh_022 :
    (nb073AlphaDummy081) ∉
      (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv) :=
  by
  simpa only [nb073AlphaDummy081] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv)
      1

theorem nb073_distinct_023 : (nb073AlphaDummy080) ≠ (nb073AlphaDummy081) := by
  simpa only [nb073AlphaDummy080, nb073AlphaDummy081] using
    (freshVar_injective
      (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_fresh_024 :
    (nb073AlphaDummy022) ∉ (((Class.cv (nb073AlphaDummy015))).fv) := by
  simpa only [nb073AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy015))).fv) 0

theorem nb073_fresh_025 :
    (nb073AlphaDummy023) ∉ (((Class.cv (nb073AlphaDummy015))).fv) := by
  simpa only [nb073AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy015))).fv) 1

theorem nb073_distinct_026 : (nb073AlphaDummy022) ≠ (nb073AlphaDummy023) := by
  simpa only [nb073AlphaDummy022, nb073AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy015))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_027 (x : Var) (y : Var) :
    (nb073AlphaDummy082 x y) ∉
      (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy017 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy017 x y))).fv)
      0

theorem nb073_fresh_028 (x : Var) (y : Var) :
    (nb073AlphaDummy083 x y) ∉
      (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy017 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy083] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy017 x y))).fv)
      1

theorem nb073_distinct_029 (x : Var) (y : Var) :
    (nb073AlphaDummy082 x y) ≠ (nb073AlphaDummy083 x y) := by
  simpa only [nb073AlphaDummy082, nb073AlphaDummy083] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_030 (x : Var) (y : Var) :
    (nb073AlphaDummy024 x y) ∉ (((Class.cv (nb073AlphaDummy017 x y))).fv) := by
  simpa only [nb073AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy017 x y))).fv) 0

theorem nb073_fresh_031 (x : Var) (y : Var) :
    (nb073AlphaDummy025 x y) ∉ (((Class.cv (nb073AlphaDummy017 x y))).fv) := by
  simpa only [nb073AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy017 x y))).fv) 1

theorem nb073_distinct_032 (x : Var) (y : Var) :
    (nb073AlphaDummy024 x y) ≠ (nb073AlphaDummy025 x y) := by
  simpa only [nb073AlphaDummy024, nb073AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy017 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb073_fresh_033 :
    (nb073AlphaDummy028) ∉
      (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C073C001Part002`. -/


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

theorem nb073_fresh_034 :
    (nb073AlphaDummy029) ∉
      (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) 1

theorem nb073_fresh_035 :
    (nb073AlphaDummy030) ∉
      (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) 2

theorem nb073_distinct_036 : (nb073AlphaDummy028) ≠ (nb073AlphaDummy029) := by
  simpa only [nb073AlphaDummy028, nb073AlphaDummy029] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb073_distinct_037 : (nb073AlphaDummy028) ≠ (nb073AlphaDummy030) := by
  simpa only [nb073AlphaDummy028, nb073AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb073_distinct_038 : (nb073AlphaDummy029) ≠ (nb073AlphaDummy030) := by
  simpa only [nb073AlphaDummy029, nb073AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb073_fresh_039 (x : Var) (y : Var) :
    (nb073AlphaDummy031 x y) ∉
      (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb073_fresh_040 (x : Var) (y : Var) :
    (nb073AlphaDummy032 x y) ∉
      (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb073_fresh_041 (x : Var) (y : Var) :
    (nb073AlphaDummy033 x y) ∉
      (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb073_distinct_042 (x : Var) (y : Var) :
    (nb073AlphaDummy031 x y) ≠ (nb073AlphaDummy032 x y) := by
  simpa only [nb073AlphaDummy031, nb073AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_distinct_043 (x : Var) (y : Var) :
    (nb073AlphaDummy031 x y) ≠ (nb073AlphaDummy033 x y) := by
  simpa only [nb073AlphaDummy031, nb073AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb073_distinct_044 (x : Var) (y : Var) :
    (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy033 x y) := by
  simpa only [nb073AlphaDummy032, nb073AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb073_fresh_045 :
    (nb073AlphaDummy040) ∉
      (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy029))).fv) :=
  by
  simpa only [nb073AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy029))).fv)
      0

theorem nb073_fresh_046 :
    (nb073AlphaDummy036) ∉
      (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv) :=
  by
  simpa only [nb073AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv)
      0

theorem nb073_fresh_047 :
    (nb073AlphaDummy042) ∉
      (((Class.cv (nb073AlphaDummy030))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv) :=
  by
  simpa only [nb073AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy030))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv)
      0

theorem nb073_fresh_048 (x : Var) (y : Var) :
    (nb073AlphaDummy041 x y) ∉
      (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy032 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy032 x y))).fv)
      0

theorem nb073_fresh_049 (x : Var) (y : Var) :
    (nb073AlphaDummy037 x y) ∉
      (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy033 x y))).fv)
      0

theorem nb073_fresh_050 (x : Var) (y : Var) :
    (nb073AlphaDummy043 x y) ∉
      (((Class.cv (nb073AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy033 x y))).fv)
      0

theorem nb073_fresh_051 :
    (nb073AlphaDummy056) ∉
      (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) 0

theorem nb073_fresh_052 :
    (nb073AlphaDummy057) ∉
      (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) 1

theorem nb073_fresh_053 :
    (nb073AlphaDummy058) ∉
      (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) 2

theorem nb073_distinct_054 : (nb073AlphaDummy056) ≠ (nb073AlphaDummy057) := by
  simpa only [nb073AlphaDummy056, nb073AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb073_distinct_055 : (nb073AlphaDummy056) ≠ (nb073AlphaDummy058) := by
  simpa only [nb073AlphaDummy056, nb073AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb073_distinct_056 : (nb073AlphaDummy057) ≠ (nb073AlphaDummy058) := by
  simpa only [nb073AlphaDummy057, nb073AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb073_fresh_057 (x : Var) (y : Var) :
    (nb073AlphaDummy059 x y) ∉
      (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb073_fresh_058 (x : Var) (y : Var) :
    (nb073AlphaDummy060 x y) ∉
      (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb073_fresh_059 (x : Var) (y : Var) :
    (nb073AlphaDummy061 x y) ∉
      (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb073_distinct_060 (x : Var) (y : Var) :
    (nb073AlphaDummy059 x y) ≠ (nb073AlphaDummy060 x y) := by
  simpa only [nb073AlphaDummy059, nb073AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_distinct_061 (x : Var) (y : Var) :
    (nb073AlphaDummy059 x y) ≠ (nb073AlphaDummy061 x y) := by
  simpa only [nb073AlphaDummy059, nb073AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb073_distinct_062 (x : Var) (y : Var) :
    (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy061 x y) := by
  simpa only [nb073AlphaDummy060, nb073AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb073_fresh_063 :
    (nb073AlphaDummy068) ∉
      (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy057))).fv) :=
  by
  simpa only [nb073AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy057))).fv)
      0

theorem nb073_fresh_064 :
    (nb073AlphaDummy064) ∉
      (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv) :=
  by
  simpa only [nb073AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv)
      0

theorem nb073_fresh_065 :
    (nb073AlphaDummy070) ∉
      (((Class.cv (nb073AlphaDummy058))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv) :=
  by
  simpa only [nb073AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy058))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv)
      0

theorem nb073_fresh_066 (x : Var) (y : Var) :
    (nb073AlphaDummy069 x y) ∉
      (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy060 x y))).fv)
      0

theorem nb073_fresh_067 (x : Var) (y : Var) :
    (nb073AlphaDummy065 x y) ∉
      (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy061 x y))).fv)
      0

theorem nb073_fresh_068 (x : Var) (y : Var) :
    (nb073AlphaDummy071 x y) ∉
      (((Class.cv (nb073AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy061 x y))).fv)
      0

theorem nb073_fresh_069 :
    (nb073AlphaDummy088) ∉ (((Class.cv (nb073AlphaDummy081))).fv) := by
  simpa only [nb073AlphaDummy088] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy081))).fv) 0

theorem nb073_fresh_070 :
    (nb073AlphaDummy089) ∉ (((Class.cv (nb073AlphaDummy081))).fv) := by
  simpa only [nb073AlphaDummy089] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy081))).fv) 1

theorem nb073_distinct_071 : (nb073AlphaDummy088) ≠ (nb073AlphaDummy089) := by
  simpa only [nb073AlphaDummy088, nb073AlphaDummy089] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy081))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_072 (x : Var) (y : Var) :
    (nb073AlphaDummy090 x y) ∉ (((Class.cv (nb073AlphaDummy083 x y))).fv) := by
  simpa only [nb073AlphaDummy090] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy083 x y))).fv) 0

theorem nb073_fresh_073 (x : Var) (y : Var) :
    (nb073AlphaDummy091 x y) ∉ (((Class.cv (nb073AlphaDummy083 x y))).fv) := by
  simpa only [nb073AlphaDummy091] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy083 x y))).fv) 1

theorem nb073_distinct_074 (x : Var) (y : Var) :
    (nb073AlphaDummy090 x y) ≠ (nb073AlphaDummy091 x y) := by
  simpa only [nb073AlphaDummy090, nb073AlphaDummy091] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy083 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb073_fresh_075 :
    (nb073AlphaDummy094) ∉
      (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy094] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) 0

theorem nb073_fresh_076 :
    (nb073AlphaDummy095) ∉
      (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy095] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) 1

theorem nb073_fresh_077 :
    (nb073AlphaDummy096) ∉
      (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) 2

theorem nb073_distinct_078 : (nb073AlphaDummy094) ≠ (nb073AlphaDummy095) := by
  simpa only [nb073AlphaDummy094, nb073AlphaDummy095] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb073_distinct_079 : (nb073AlphaDummy094) ≠ (nb073AlphaDummy096) := by
  simpa only [nb073AlphaDummy094, nb073AlphaDummy096] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb073_distinct_080 : (nb073AlphaDummy095) ≠ (nb073AlphaDummy096) := by
  simpa only [nb073AlphaDummy095, nb073AlphaDummy096] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb073_fresh_081 (x : Var) (y : Var) :
    (nb073AlphaDummy097 x y) ∉
      (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb073_fresh_082 (x : Var) (y : Var) :
    (nb073AlphaDummy098 x y) ∉
      (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy098] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb073_fresh_083 (x : Var) (y : Var) :
    (nb073AlphaDummy099 x y) ∉
      (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb073AlphaDummy099] using
    freshVar_not_mem (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb073_distinct_084 (x : Var) (y : Var) :
    (nb073AlphaDummy097 x y) ≠ (nb073AlphaDummy098 x y) := by
  simpa only [nb073AlphaDummy097, nb073AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_distinct_085 (x : Var) (y : Var) :
    (nb073AlphaDummy097 x y) ≠ (nb073AlphaDummy099 x y) := by
  simpa only [nb073AlphaDummy097, nb073AlphaDummy099] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb073_distinct_086 (x : Var) (y : Var) :
    (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy099 x y) := by
  simpa only [nb073AlphaDummy098, nb073AlphaDummy099] using
    (freshVar_injective (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb073_fresh_087 :
    (nb073AlphaDummy106) ∉
      (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy095))).fv) :=
  by
  simpa only [nb073AlphaDummy106] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy095))).fv)
      0

theorem nb073_fresh_088 :
    (nb073AlphaDummy102) ∉
      (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv) :=
  by
  simpa only [nb073AlphaDummy102] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv)
      0

theorem nb073_fresh_089 :
    (nb073AlphaDummy108) ∉
      (((Class.cv (nb073AlphaDummy096))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv) :=
  by
  simpa only [nb073AlphaDummy108] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy096))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv)
      0

theorem nb073_fresh_090 (x : Var) (y : Var) :
    (nb073AlphaDummy107 x y) ∉
      (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy098 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy107] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy098 x y))).fv)
      0

theorem nb073_fresh_091 (x : Var) (y : Var) :
    (nb073AlphaDummy103 x y) ∉
      (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy099 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy103] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy099 x y))).fv)
      0

theorem nb073_fresh_092 (x : Var) (y : Var) :
    (nb073AlphaDummy109 x y) ∉
      (((Class.cv (nb073AlphaDummy099 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy099 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy109] using
    freshVar_not_mem
      (((Class.cv (nb073AlphaDummy099 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy099 x y))).fv)
      0

theorem nb073_fresh_093 (x : Var) (y : Var) :
    (nb073AlphaDummy016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb073AlphaDummy016] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb073_fresh_094 (x : Var) (y : Var) :
    (nb073AlphaDummy017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb073AlphaDummy017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb073_distinct_095 (x : Var) (y : Var) :
    (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy017 x y) := by
  simpa only [nb073AlphaDummy016, nb073AlphaDummy017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_096 :
    (nb073AlphaDummy026) ∉
      (((Wff.classMem (Class.cv (nb073AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy022))).fv) :=
  by
  simpa only [nb073AlphaDummy026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy022))).fv)
      0

theorem nb073_fresh_097 (x : Var) (y : Var) :
    (nb073AlphaDummy027 x y) ∉
      (((Wff.classMem (Class.cv (nb073AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy024 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy024 x y))).fv)
      0

theorem nb073_fresh_098 :
    (nb073AlphaDummy054) ∉
      (((Wff.classMem (Class.cv (nb073AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy050))).fv) :=
  by
  simpa only [nb073AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy050))).fv)
      0

theorem nb073_fresh_099 (x : Var) (y : Var) :
    (nb073AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb073AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy052 x y))).fv)
      0

theorem nb073_fresh_100 :
    (nb073AlphaDummy092) ∉
      (((Wff.classMem (Class.cv (nb073AlphaDummy088)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy088)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy088))).fv) :=
  by
  simpa only [nb073AlphaDummy092] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073AlphaDummy088)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy088)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy088))).fv)
      0

theorem nb073_fresh_101 (x : Var) (y : Var) :
    (nb073AlphaDummy093 x y) ∉
      (((Wff.classMem (Class.cv (nb073AlphaDummy090 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy090 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy090 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy093] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb073AlphaDummy090 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy090 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy090 x y))).fv)
      0

theorem nb073_fresh_102 :
    (nb073AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
                (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCphi (Class.cv (nb073AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy006)
              (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb073AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
                (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCphi (Class.cv (nb073AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy006)
              (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb073_fresh_103 (x : Var) (y : Var) :
    (nb073AlphaDummy011 x y) ∉
      (((synCcompl (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCphi (Class.cv (nb073AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb073AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCphi (Class.cv (nb073AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb073_fresh_104 :
    (nb073AlphaDummy018) ∉
      (((synCcompl (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCphi (Class.cv (nb073AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb073AlphaDummy018] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCphi (Class.cv (nb073AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb073_fresh_105 (x : Var) (y : Var) :
    (nb073AlphaDummy019 x y) ∉
      (((synCcompl (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCphi (Class.cv (nb073AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb073AlphaDummy019] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCphi (Class.cv (nb073AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb073_fresh_106 :
    (nb073AlphaDummy084) ∉
      (((synCcompl (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCphi (Class.cv (nb073AlphaDummy081)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb073AlphaDummy084] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCphi (Class.cv (nb073AlphaDummy081)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb073_fresh_107 (x : Var) (y : Var) :
    (nb073AlphaDummy085 x y) ∉
      (((synCcompl (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCphi (Class.cv (nb073AlphaDummy083 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb073AlphaDummy085] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCphi (Class.cv (nb073AlphaDummy083 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb073_fresh_108 :
    (nb073AlphaDummy038) ∉
      (((synCcompl (Class.cv (nb073AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy030)))).fv) :=
  by
  simpa only [nb073AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb073AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy030)))).fv)
      0

theorem nb073_fresh_109 (x : Var) (y : Var) :
    (nb073AlphaDummy039 x y) ∉
      (((synCcompl (Class.cv (nb073AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb073AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy033 x y)))).fv)
      0

theorem nb073_fresh_110 :
    (nb073AlphaDummy066) ∉
      (((synCcompl (Class.cv (nb073AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy058)))).fv) :=
  by
  simpa only [nb073AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb073AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy058)))).fv)
      0

theorem nb073_fresh_111 (x : Var) (y : Var) :
    (nb073AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb073AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb073AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy061 x y)))).fv)
      0

theorem nb073_fresh_112 :
    (nb073AlphaDummy104) ∉
      (((synCcompl (Class.cv (nb073AlphaDummy095)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy096)))).fv) :=
  by
  simpa only [nb073AlphaDummy104] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb073AlphaDummy095)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy096)))).fv)
      0

theorem nb073_fresh_113 (x : Var) (y : Var) :
    (nb073AlphaDummy105 x y) ∉
      (((synCcompl (Class.cv (nb073AlphaDummy098 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy099 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy105] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb073AlphaDummy098 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy099 x y)))).fv)
      0

theorem nb073_fresh_114 :
    (nb073AlphaDummy074) ∉
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb073AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb073_fresh_115 (x : Var) (y : Var) :
    (nb073AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb073AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb073_fresh_116 :
    (nb073AlphaDummy046) ∉
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb073AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb073_fresh_117 (x : Var) (y : Var) :
    (nb073AlphaDummy047 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb073AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb073_fresh_118 :
    (nb073AlphaDummy112) ∉
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy081))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb073AlphaDummy112] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy081))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb073_fresh_119 (x : Var) (y : Var) :
    (nb073AlphaDummy113 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy083 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb073AlphaDummy113] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy083 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb073_fresh_120 :
    (nb073AlphaDummy034) ∉
      (((synCnin (Class.cv (nb073AlphaDummy029)) (Class.cv (nb073AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy029))
            (Class.cv (nb073AlphaDummy030)))).fv) :=
  by
  simpa only [nb073AlphaDummy034] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb073AlphaDummy029)) (Class.cv (nb073AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy029)) (Class.cv (nb073AlphaDummy030)))).fv)
      0

theorem nb073_fresh_121 (x : Var) (y : Var) :
    (nb073AlphaDummy035 x y) ∉
      (((synCnin (Class.cv (nb073AlphaDummy032 x y))
            (Class.cv (nb073AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy032 x y))
            (Class.cv (nb073AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy035] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb073AlphaDummy032 x y))
            (Class.cv (nb073AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy032 x y))
            (Class.cv (nb073AlphaDummy033 x y)))).fv)
      0

theorem nb073_fresh_122 :
    (nb073AlphaDummy062) ∉
      (((synCnin (Class.cv (nb073AlphaDummy057)) (Class.cv (nb073AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy057))
            (Class.cv (nb073AlphaDummy058)))).fv) :=
  by
  simpa only [nb073AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb073AlphaDummy057)) (Class.cv (nb073AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy057)) (Class.cv (nb073AlphaDummy058)))).fv)
      0

theorem nb073_fresh_123 (x : Var) (y : Var) :
    (nb073AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb073AlphaDummy060 x y))
            (Class.cv (nb073AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy060 x y))
            (Class.cv (nb073AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb073AlphaDummy060 x y))
            (Class.cv (nb073AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy060 x y))
            (Class.cv (nb073AlphaDummy061 x y)))).fv)
      0

theorem nb073_fresh_124 :
    (nb073AlphaDummy100) ∉
      (((synCnin (Class.cv (nb073AlphaDummy095)) (Class.cv (nb073AlphaDummy096)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy095))
            (Class.cv (nb073AlphaDummy096)))).fv) :=
  by
  simpa only [nb073AlphaDummy100] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb073AlphaDummy095)) (Class.cv (nb073AlphaDummy096)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy095)) (Class.cv (nb073AlphaDummy096)))).fv)
      0

theorem nb073_fresh_125 (x : Var) (y : Var) :
    (nb073AlphaDummy101 x y) ∉
      (((synCnin (Class.cv (nb073AlphaDummy098 x y))
            (Class.cv (nb073AlphaDummy099 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy098 x y))
            (Class.cv (nb073AlphaDummy099 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy101] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb073AlphaDummy098 x y))
            (Class.cv (nb073AlphaDummy099 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy098 x y))
            (Class.cv (nb073AlphaDummy099 x y)))).fv)
      0

theorem nb073_fresh_126 :
    (nb073AlphaDummy006) ∉
      (((synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv ∪
        ((Class.cv (nb073AlphaDummy002))).fv) :=
  by
  simpa only [nb073AlphaDummy006] using
    freshVar_not_mem
      (((synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv ∪
        ((Class.cv (nb073AlphaDummy002))).fv)
      0

theorem nb073_fresh_127 :
    (nb073AlphaDummy007) ∉
      (((synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv ∪
        ((Class.cv (nb073AlphaDummy002))).fv) :=
  by
  simpa only [nb073AlphaDummy007] using
    freshVar_not_mem
      (((synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv ∪
        ((Class.cv (nb073AlphaDummy002))).fv)
      1

theorem nb073_distinct_128 : (nb073AlphaDummy006) ≠ (nb073AlphaDummy007) := by
  simpa only [nb073AlphaDummy006, nb073AlphaDummy007] using
    (freshVar_injective (((synCop (Class.cv (nb073AlphaDummy000))
            (Class.cv (nb073AlphaDummy001)))).fv ∪ ((Class.cv (nb073AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb073_fresh_129 (x : Var) (y : Var) :
    (nb073AlphaDummy008 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy008] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb073AlphaDummy003 x y))).fv)
      0

theorem nb073_fresh_130 (x : Var) (y : Var) :
    (nb073AlphaDummy009 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb073AlphaDummy009] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb073AlphaDummy003 x y))).fv)
      1

theorem nb073_distinct_131 (x : Var) (y : Var) :
    (nb073AlphaDummy008 x y) ≠ (nb073AlphaDummy009 x y) := by
  simpa only [nb073AlphaDummy008, nb073AlphaDummy009] using
    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073AlphaDummy003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb073_fresh_132 :
    (nb073AlphaDummy076) ∉
      (((synCphi (Class.cv (nb073AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy007)))).fv) :=
  by
  simpa only [nb073AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb073AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy007)))).fv)
      0

theorem nb073_fresh_133 (x : Var) (y : Var) :
    (nb073AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb073AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy009 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb073AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy009 x y)))).fv)
      0

theorem nb073_fresh_134 :
    (nb073AlphaDummy048) ∉
      (((synCphi (Class.cv (nb073AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy015)))).fv) :=
  by
  simpa only [nb073AlphaDummy048] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb073AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy015)))).fv)
      0

theorem nb073_fresh_135 (x : Var) (y : Var) :
    (nb073AlphaDummy049 x y) ∉
      (((synCphi (Class.cv (nb073AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy017 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy049] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb073AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy017 x y)))).fv)
      0

theorem nb073_fresh_136 :
    (nb073AlphaDummy114) ∉
      (((synCphi (Class.cv (nb073AlphaDummy081)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy081)))).fv) :=
  by
  simpa only [nb073AlphaDummy114] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb073AlphaDummy081)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy081)))).fv)
      0

theorem nb073_fresh_137 (x : Var) (y : Var) :
    (nb073AlphaDummy115 x y) ∉
      (((synCphi (Class.cv (nb073AlphaDummy083 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy083 x y)))).fv) :=
  by
  simpa only [nb073AlphaDummy115] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb073AlphaDummy083 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy083 x y)))).fv)
      0

theorem nb073_fresh_138 :
    (nb073AlphaDummy002) ∉
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb073AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCxp (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv) :=
  by
  simpa only [nb073AlphaDummy002] using
    freshVar_not_mem
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb073AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCxp (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv)
      0

theorem nb073_fresh_139 :
    (nb073AlphaDummy004) ∉
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ({(nb073AlphaDummy001)} : Finset Var) ∪
          ({(nb073AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb073AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb073AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy002))
              (synCxp (Class.cv (nb073AlphaDummy000))
                (Class.cv (nb073AlphaDummy001)))))).fv) :=
  by
  simpa only [nb073AlphaDummy004] using
    freshVar_not_mem
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ({(nb073AlphaDummy001)} : Finset Var) ∪
          ({(nb073AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb073AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb073AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy002))
              (synCxp (Class.cv (nb073AlphaDummy000))
                (Class.cv (nb073AlphaDummy001)))))).fv)
      0

theorem nb073_fresh_140 :
    (nb073AlphaDummy078) ∉
      (({(nb073AlphaDummy014)} : Finset Var) ∪ ({(nb073AlphaDummy015)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy014))
              (Class.cv (nb073AlphaDummy000)))
            (Wff.classMem (Class.cv (nb073AlphaDummy015))
              (Class.cv (nb073AlphaDummy001))))).fv) :=
  by
  simpa only [nb073AlphaDummy078] using
    freshVar_not_mem
      (({(nb073AlphaDummy014)} : Finset Var) ∪ ({(nb073AlphaDummy015)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy014))
              (Class.cv (nb073AlphaDummy000)))
            (Wff.classMem (Class.cv (nb073AlphaDummy015))
              (Class.cv (nb073AlphaDummy001))))).fv)
      0

theorem nb073_fresh_141 (x : Var) (y : Var) :
    (nb073AlphaDummy079 x y) ∉
      (({(nb073AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb073AlphaDummy017 x y)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073AlphaDummy017 x y)) (Class.cv y)))).fv) :=
  by
  simpa only [nb073AlphaDummy079] using
    freshVar_not_mem
      (({(nb073AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb073AlphaDummy017 x y)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073AlphaDummy017 x y)) (Class.cv y)))).fv)
      0

theorem nb073_fresh_142 (x : Var) (y : Var) :
    (nb073AlphaDummy003 x y) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCxp (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb073AlphaDummy003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCxp (Class.cv x) (Class.cv y))).fv)
      0

theorem nb073_fresh_143 (x : Var) (y : Var) :
    (nb073AlphaDummy005 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy003 x y))
              (synCxp (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb073AlphaDummy005] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy003 x y))
              (synCxp (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb073_fresh_144 : (nb073AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb073AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb073_fresh_145 : (nb073AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb073AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb073_distinct_146 : (nb073AlphaDummy000) ≠ (nb073AlphaDummy001) := by
  simpa only [nb073AlphaDummy000, nb073AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb073_support_mem_0000 :
    (nb073AlphaDummy000) ∈
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ({(nb073AlphaDummy001)} : Finset Var) ∪
          ({(nb073AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb073AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb073AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy002))
              (synCxp (Class.cv (nb073AlphaDummy000))
                (Class.cv (nb073AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy003 x y))
              (synCxp (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0002 :
    (nb073AlphaDummy001) ∈
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ({(nb073AlphaDummy001)} : Finset Var) ∪
          ({(nb073AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb073AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb073AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy002))
              (synCxp (Class.cv (nb073AlphaDummy000))
                (Class.cv (nb073AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy003 x y))
              (synCxp (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0004 :
    (nb073AlphaDummy002) ∈
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ({(nb073AlphaDummy001)} : Finset Var) ∪
          ({(nb073AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb073AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb073AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy002))
              (synCxp (Class.cv (nb073AlphaDummy000))
                (Class.cv (nb073AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0005 (x : Var) (y : Var) :
    (nb073AlphaDummy003 x y) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb073AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb073AlphaDummy003 x y))
              (synCxp (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0006 :
    (nb073AlphaDummy000) ∈
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb073AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCxp (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv) :=
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

theorem nb073_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCxp (Class.cv x) (Class.cv y))).fv) :=
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

theorem nb073_support_mem_0008 :
    (nb073AlphaDummy000) ∈
      (((synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv ∪
        ((Class.cv (nb073AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0009 :
    (nb073AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
                (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCphi (Class.cv (nb073AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy006)
              (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy006) from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy007) from (by
            unfold nb073AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0010 (x : Var) (y : Var) :
    x ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0011 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCphi (Class.cv (nb073AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb073AlphaDummy009 x y) from (by
            unfold nb073AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0012 :
    (nb073AlphaDummy000) ∈
      (((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))).fv ∪
        ((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy006) from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy007) from (by
            unfold nb073AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb073AlphaDummy009 x y) from (by
            unfold nb073AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0014 :
    (nb073AlphaDummy000) ∈
      (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0015 :
    (nb073AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCphi (Class.cv (nb073AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy014) from (by
          unfold nb073AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy015) from (by
            unfold nb073AlphaDummy015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCphi (Class.cv (nb073AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb073AlphaDummy016 x y) from (by
          unfold nb073AlphaDummy016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb073AlphaDummy017 x y) from (by
            unfold nb073AlphaDummy017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0018 :
    (nb073AlphaDummy000) ∈
      (((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCphi (Class.cv (nb073AlphaDummy015))))))).fv ∪
        ((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCphi (Class.cv (nb073AlphaDummy015))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy014) from (by
          unfold nb073AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy015) from (by
            unfold nb073AlphaDummy015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCphi (Class.cv (nb073AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCphi (Class.cv (nb073AlphaDummy017 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb073AlphaDummy016 x y) from (by
          unfold nb073AlphaDummy016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb073AlphaDummy017 x y) from (by
            unfold nb073AlphaDummy017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0020 :
    (nb073AlphaDummy015) ∈ (((Class.cv (nb073AlphaDummy015))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0021 (x : Var) (y : Var) :
    (nb073AlphaDummy017 x y) ∈ (((Class.cv (nb073AlphaDummy017 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0022 :
    (nb073AlphaDummy022) ∈
      (((Wff.classMem (Class.cv (nb073AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy022))).fv) :=
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

theorem nb073_support_mem_0023 (x : Var) (y : Var) :
    (nb073AlphaDummy024 x y) ∈
      (((Wff.classMem (Class.cv (nb073AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy024 x y))).fv) :=
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

theorem nb073_support_mem_0024 :
    (nb073AlphaDummy022) ∈
      (((Class.cv (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0025 (x : Var) (y : Var) :
    (nb073AlphaDummy024 x y) ∈
      (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0026 :
    (nb073AlphaDummy029) ∈
      (((synCnin (Class.cv (nb073AlphaDummy029)) (Class.cv (nb073AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy029))
            (Class.cv (nb073AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0027 (x : Var) (y : Var) :
    (nb073AlphaDummy032 x y) ∈
      (((synCnin (Class.cv (nb073AlphaDummy032 x y))
            (Class.cv (nb073AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy032 x y))
            (Class.cv (nb073AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0028 :
    (nb073AlphaDummy029) ∈
      (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0029 (x : Var) (y : Var) :
    (nb073AlphaDummy032 x y) ∈
      (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0030 :
    (nb073AlphaDummy030) ∈
      (((synCnin (Class.cv (nb073AlphaDummy029)) (Class.cv (nb073AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy029))
            (Class.cv (nb073AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0031 (x : Var) (y : Var) :
    (nb073AlphaDummy033 x y) ∈
      (((synCnin (Class.cv (nb073AlphaDummy032 x y))
            (Class.cv (nb073AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy032 x y))
            (Class.cv (nb073AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0032 :
    (nb073AlphaDummy030) ∈
      (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C073C001Part003`. -/


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

theorem nb073_support_mem_0033 (x : Var) (y : Var) :
    (nb073AlphaDummy033 x y) ∈
      (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0034 :
    (nb073AlphaDummy029) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0035 (x : Var) (y : Var) :
    (nb073AlphaDummy032 x y) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0036 :
    (nb073AlphaDummy029) ∈
      (((Class.cv (nb073AlphaDummy029))).fv ∪ ((Class.cv (nb073AlphaDummy029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0037 (x : Var) (y : Var) :
    (nb073AlphaDummy032 x y) ∈
      (((Class.cv (nb073AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy032 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0038 :
    (nb073AlphaDummy030) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0039 (x : Var) (y : Var) :
    (nb073AlphaDummy033 x y) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0040 :
    (nb073AlphaDummy030) ∈
      (((Class.cv (nb073AlphaDummy030))).fv ∪ ((Class.cv (nb073AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0041 (x : Var) (y : Var) :
    (nb073AlphaDummy033 x y) ∈
      (((Class.cv (nb073AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0042 :
    (nb073AlphaDummy001) ∈
      (({(nb073AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb073AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCxp (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0043 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCxp (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0044 :
    (nb073AlphaDummy001) ∈
      (((synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv ∪
        ((Class.cv (nb073AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0045 :
    (nb073AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
                (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCphi (Class.cv (nb073AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy006)
              (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy006) from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy007) from (by
            unfold nb073AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0046 (x : Var) (y : Var) :
    y ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCphi (Class.cv (nb073AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb073AlphaDummy009 x y) from (by
            unfold nb073AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0048 :
    (nb073AlphaDummy001) ∈
      (((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))).fv ∪
        ((Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy006) from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy007) from (by
            unfold nb073AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0049 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb073AlphaDummy009 x y) from (by
            unfold nb073AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0050 :
    (nb073AlphaDummy001) ∈
      (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0051 :
    (nb073AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCphi (Class.cv (nb073AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy014) from (by
          unfold nb073AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy015) from (by
            unfold nb073AlphaDummy015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCphi (Class.cv (nb073AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb073AlphaDummy016 x y) from (by
          unfold nb073AlphaDummy016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb073AlphaDummy017 x y) from (by
            unfold nb073AlphaDummy017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0054 :
    (nb073AlphaDummy001) ∈
      (((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy001))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCun (synCphi (Class.cv (nb073AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy014) from (by
          unfold nb073AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy015) from (by
            unfold nb073AlphaDummy015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb073AlphaDummy016 x y) from (by
          unfold nb073AlphaDummy016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb073AlphaDummy017 x y) from (by
            unfold nb073AlphaDummy017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0056 :
    (nb073AlphaDummy015) ∈
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0057 (x : Var) (y : Var) :
    (nb073AlphaDummy017 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0058 :
    (nb073AlphaDummy015) ∈
      (((synCphi (Class.cv (nb073AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy015)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0059 (x : Var) (y : Var) :
    (nb073AlphaDummy017 x y) ∈
      (((synCphi (Class.cv (nb073AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy017 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0060 :
    (nb073AlphaDummy007) ∈ (((Class.cv (nb073AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0061 (x : Var) (y : Var) :
    (nb073AlphaDummy009 x y) ∈ (((Class.cv (nb073AlphaDummy009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0062 :
    (nb073AlphaDummy050) ∈
      (((Wff.classMem (Class.cv (nb073AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy050))).fv) :=
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

theorem nb073_support_mem_0063 (x : Var) (y : Var) :
    (nb073AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb073AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy052 x y))).fv) :=
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

theorem nb073_support_mem_0064 :
    (nb073AlphaDummy050) ∈
      (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0065 (x : Var) (y : Var) :
    (nb073AlphaDummy052 x y) ∈
      (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0066 :
    (nb073AlphaDummy057) ∈
      (((synCnin (Class.cv (nb073AlphaDummy057)) (Class.cv (nb073AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy057))
            (Class.cv (nb073AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0067 (x : Var) (y : Var) :
    (nb073AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb073AlphaDummy060 x y))
            (Class.cv (nb073AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy060 x y))
            (Class.cv (nb073AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0068 :
    (nb073AlphaDummy057) ∈
      (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0069 (x : Var) (y : Var) :
    (nb073AlphaDummy060 x y) ∈
      (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0070 :
    (nb073AlphaDummy058) ∈
      (((synCnin (Class.cv (nb073AlphaDummy057)) (Class.cv (nb073AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy057))
            (Class.cv (nb073AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0071 (x : Var) (y : Var) :
    (nb073AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb073AlphaDummy060 x y))
            (Class.cv (nb073AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy060 x y))
            (Class.cv (nb073AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0072 :
    (nb073AlphaDummy058) ∈
      (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0073 (x : Var) (y : Var) :
    (nb073AlphaDummy061 x y) ∈
      (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0074 :
    (nb073AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0075 (x : Var) (y : Var) :
    (nb073AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0076 :
    (nb073AlphaDummy057) ∈
      (((Class.cv (nb073AlphaDummy057))).fv ∪ ((Class.cv (nb073AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0077 (x : Var) (y : Var) :
    (nb073AlphaDummy060 x y) ∈
      (((Class.cv (nb073AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0078 :
    (nb073AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0079 (x : Var) (y : Var) :
    (nb073AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0080 :
    (nb073AlphaDummy058) ∈
      (((Class.cv (nb073AlphaDummy058))).fv ∪ ((Class.cv (nb073AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0081 (x : Var) (y : Var) :
    (nb073AlphaDummy061 x y) ∈
      (((Class.cv (nb073AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0082 :
    (nb073AlphaDummy002) ∈
      (((synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))).fv ∪
        ((Class.cv (nb073AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0083 :
    (nb073AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
                (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCphi (Class.cv (nb073AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy006)
              (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy006) from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy007) from (by
            unfold nb073AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0084 (x : Var) (y : Var) :
    (nb073AlphaDummy003 x y) ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb073AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0085 (x : Var) (y : Var) :
    (nb073AlphaDummy003 x y) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCphi (Class.cv (nb073AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy009 x y) from (by
            unfold nb073AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0086 :
    (nb073AlphaDummy002) ∈
      (((Class.cab (nb073AlphaDummy006)
            (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy006)
            (synWrex (nb073AlphaDummy007) (Class.cv (nb073AlphaDummy002))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCun (synCphi (Class.cv (nb073AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy006) from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy007) from (by
            unfold nb073AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0087 (x : Var) (y : Var) :
    (nb073AlphaDummy003 x y) ∈
      (((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (Class.cv (nb073AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy009 x y) from (by
            unfold nb073AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0088 :
    (nb073AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0089 (x : Var) (y : Var) :
    (nb073AlphaDummy009 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0090 :
    (nb073AlphaDummy007) ∈
      (((synCphi (Class.cv (nb073AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0091 (x : Var) (y : Var) :
    (nb073AlphaDummy009 x y) ∈
      (((synCphi (Class.cv (nb073AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0092 :
    (nb073AlphaDummy014) ∈
      (({(nb073AlphaDummy014)} : Finset Var) ∪ ({(nb073AlphaDummy015)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy014))
              (Class.cv (nb073AlphaDummy000)))
            (Wff.classMem (Class.cv (nb073AlphaDummy015))
              (Class.cv (nb073AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0093 (x : Var) (y : Var) :
    (nb073AlphaDummy016 x y) ∈
      (({(nb073AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb073AlphaDummy017 x y)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073AlphaDummy017 x y)) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0094 :
    (nb073AlphaDummy015) ∈
      (({(nb073AlphaDummy014)} : Finset Var) ∪ ({(nb073AlphaDummy015)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy014))
              (Class.cv (nb073AlphaDummy000)))
            (Wff.classMem (Class.cv (nb073AlphaDummy015))
              (Class.cv (nb073AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0095 (x : Var) (y : Var) :
    (nb073AlphaDummy017 x y) ∈
      (({(nb073AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb073AlphaDummy017 x y)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073AlphaDummy017 x y)) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0096 :
    (nb073AlphaDummy014) ∈
      (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0097 :
    (nb073AlphaDummy014) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCphi (Class.cv (nb073AlphaDummy081)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy080) from (by
          unfold nb073AlphaDummy080;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy081) from (by
            unfold nb073AlphaDummy081;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0098 (x : Var) (y : Var) :
    (nb073AlphaDummy016 x y) ∈
      (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0099 (x : Var) (y : Var) :
    (nb073AlphaDummy016 x y) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCphi (Class.cv (nb073AlphaDummy083 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy082 x y) from (by
          unfold nb073AlphaDummy082;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy083 x y) from (by
            unfold nb073AlphaDummy083;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0100 :
    (nb073AlphaDummy014) ∈
      (((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCphi (Class.cv (nb073AlphaDummy081))))))).fv ∪
        ((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCphi (Class.cv (nb073AlphaDummy081))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy080) from (by
          unfold nb073AlphaDummy080;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy081) from (by
            unfold nb073AlphaDummy081;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0101 (x : Var) (y : Var) :
    (nb073AlphaDummy016 x y) ∈
      (((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCphi (Class.cv (nb073AlphaDummy083 x y))))))).fv ∪
        ((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCphi (Class.cv (nb073AlphaDummy083 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy082 x y) from (by
          unfold nb073AlphaDummy082;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy083 x y) from (by
            unfold nb073AlphaDummy083;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0102 :
    (nb073AlphaDummy081) ∈ (((Class.cv (nb073AlphaDummy081))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0103 (x : Var) (y : Var) :
    (nb073AlphaDummy083 x y) ∈ (((Class.cv (nb073AlphaDummy083 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0104 :
    (nb073AlphaDummy088) ∈
      (((Wff.classMem (Class.cv (nb073AlphaDummy088)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy088)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy088))).fv) :=
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

theorem nb073_support_mem_0105 (x : Var) (y : Var) :
    (nb073AlphaDummy090 x y) ∈
      (((Wff.classMem (Class.cv (nb073AlphaDummy090 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb073AlphaDummy090 x y)) (synC1c))).fv ∪
        ((Class.cv (nb073AlphaDummy090 x y))).fv) :=
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

theorem nb073_support_mem_0106 :
    (nb073AlphaDummy088) ∈
      (((Class.cv (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0107 (x : Var) (y : Var) :
    (nb073AlphaDummy090 x y) ∈
      (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0108 :
    (nb073AlphaDummy095) ∈
      (((synCnin (Class.cv (nb073AlphaDummy095)) (Class.cv (nb073AlphaDummy096)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy095))
            (Class.cv (nb073AlphaDummy096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0109 (x : Var) (y : Var) :
    (nb073AlphaDummy098 x y) ∈
      (((synCnin (Class.cv (nb073AlphaDummy098 x y))
            (Class.cv (nb073AlphaDummy099 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy098 x y))
            (Class.cv (nb073AlphaDummy099 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0110 :
    (nb073AlphaDummy095) ∈
      (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0111 (x : Var) (y : Var) :
    (nb073AlphaDummy098 x y) ∈
      (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy099 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0112 :
    (nb073AlphaDummy096) ∈
      (((synCnin (Class.cv (nb073AlphaDummy095)) (Class.cv (nb073AlphaDummy096)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy095))
            (Class.cv (nb073AlphaDummy096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0113 (x : Var) (y : Var) :
    (nb073AlphaDummy099 x y) ∈
      (((synCnin (Class.cv (nb073AlphaDummy098 x y))
            (Class.cv (nb073AlphaDummy099 x y)))).fv ∪
        ((synCnin (Class.cv (nb073AlphaDummy098 x y))
            (Class.cv (nb073AlphaDummy099 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0114 :
    (nb073AlphaDummy096) ∈
      (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0115 (x : Var) (y : Var) :
    (nb073AlphaDummy099 x y) ∈
      (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy099 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0116 :
    (nb073AlphaDummy095) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy095)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0117 (x : Var) (y : Var) :
    (nb073AlphaDummy098 x y) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy098 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy099 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0118 :
    (nb073AlphaDummy095) ∈
      (((Class.cv (nb073AlphaDummy095))).fv ∪ ((Class.cv (nb073AlphaDummy095))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0119 (x : Var) (y : Var) :
    (nb073AlphaDummy098 x y) ∈
      (((Class.cv (nb073AlphaDummy098 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy098 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0120 :
    (nb073AlphaDummy096) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy095)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0121 (x : Var) (y : Var) :
    (nb073AlphaDummy099 x y) ∈
      (((synCcompl (Class.cv (nb073AlphaDummy098 x y)))).fv ∪
        ((synCcompl (Class.cv (nb073AlphaDummy099 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0122 :
    (nb073AlphaDummy096) ∈
      (((Class.cv (nb073AlphaDummy096))).fv ∪ ((Class.cv (nb073AlphaDummy096))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0123 (x : Var) (y : Var) :
    (nb073AlphaDummy099 x y) ∈
      (((Class.cv (nb073AlphaDummy099 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy099 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0124 :
    (nb073AlphaDummy015) ∈
      (((Class.cv (nb073AlphaDummy014))).fv ∪ ((Class.cv (nb073AlphaDummy015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0125 :
    (nb073AlphaDummy015) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCphi (Class.cv (nb073AlphaDummy081)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy080) from (by
          unfold nb073AlphaDummy080;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy081) from (by
            unfold nb073AlphaDummy081;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0126 (x : Var) (y : Var) :
    (nb073AlphaDummy017 x y) ∈
      (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb073AlphaDummy017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0127 (x : Var) (y : Var) :
    (nb073AlphaDummy017 x y) ∈
      (((synCcompl (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCphi (Class.cv (nb073AlphaDummy083 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy082 x y) from (by
          unfold nb073AlphaDummy082;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy083 x y) from (by
            unfold nb073AlphaDummy083;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0128 :
    (nb073AlphaDummy015) ∈
      (((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy015))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCun (synCphi (Class.cv (nb073AlphaDummy081)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy080) from (by
          unfold nb073AlphaDummy080;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy081) from (by
            unfold nb073AlphaDummy081;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0129 (x : Var) (y : Var) :
    (nb073AlphaDummy017 x y) ∈
      (((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCun (synCphi (Class.cv (nb073AlphaDummy083 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy082 x y) from (by
          unfold nb073AlphaDummy082;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy083 x y) from (by
            unfold nb073AlphaDummy083;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0130 :
    (nb073AlphaDummy081) ∈
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy081))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0131 (x : Var) (y : Var) :
    (nb073AlphaDummy083 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb073AlphaDummy083 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0132 :
    (nb073AlphaDummy081) ∈
      (((synCphi (Class.cv (nb073AlphaDummy081)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy081)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0133 (x : Var) (y : Var) :
    (nb073AlphaDummy083 x y) ∈
      (((synCphi (Class.cv (nb073AlphaDummy083 x y)))).fv ∪
        ((synCphi (Class.cv (nb073AlphaDummy083 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0134 :
    (nb073AlphaDummy000) ∈
      (({(nb073AlphaDummy014)} : Finset Var) ∪ ({(nb073AlphaDummy015)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy014))
              (Class.cv (nb073AlphaDummy000)))
            (Wff.classMem (Class.cv (nb073AlphaDummy015))
              (Class.cv (nb073AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0135 (x : Var) (y : Var) :
    x ∈
      (({(nb073AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb073AlphaDummy017 x y)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073AlphaDummy017 x y)) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0136 :
    (nb073AlphaDummy001) ∈
      (({(nb073AlphaDummy014)} : Finset Var) ∪ ({(nb073AlphaDummy015)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy014))
              (Class.cv (nb073AlphaDummy000)))
            (Wff.classMem (Class.cv (nb073AlphaDummy015))
              (Class.cv (nb073AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0137 (x : Var) (y : Var) :
    y ∈
      (({(nb073AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb073AlphaDummy017 x y)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb073AlphaDummy016 x y)) (Class.cv x))
            (Wff.classMem (Class.cv (nb073AlphaDummy017 x y)) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
