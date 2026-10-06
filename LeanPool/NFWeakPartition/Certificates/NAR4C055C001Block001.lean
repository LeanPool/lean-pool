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

/-! Certificates from `NAR4C055C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_000`. -/
@[expose]
noncomputable def nb055AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_001`. -/
@[expose]
noncomputable def nb055AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_002`. -/
@[expose]
noncomputable def nb055AlphaDummy002 : Var :=
  (freshVar (({(nb055AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
          ({(nb055AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCcom (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_003`. -/
@[expose]
noncomputable def nb055AlphaDummy003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCcom (Class.cv x) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_004`. -/
@[expose]
noncomputable def nb055AlphaDummy004 : Var :=
  (freshVar
    (({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
        ({(nb055AlphaDummy002)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
            (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
          (Wff.classEq (Class.cv (nb055AlphaDummy002))
            (synCcom (Class.cv (nb055AlphaDummy000))
              (Class.cv (nb055AlphaDummy001)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_005`. -/
@[expose]
noncomputable def nb055AlphaDummy005 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb055AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
          (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
            (synCcom (Class.cv x) (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_006`. -/
@[expose]
noncomputable def nb055AlphaDummy006 : Var :=
  (freshVar (((synCop (Class.cv (nb055AlphaDummy000))
          (Class.cv (nb055AlphaDummy001)))).fv ∪ ((Class.cv (nb055AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_007`. -/
@[expose]
noncomputable def nb055AlphaDummy007 : Var :=
  (freshVar (((synCop (Class.cv (nb055AlphaDummy000))
          (Class.cv (nb055AlphaDummy001)))).fv ∪ ((Class.cv (nb055AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_008`. -/
@[expose]
noncomputable def nb055AlphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb055AlphaDummy003 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_009`. -/
@[expose]
noncomputable def nb055AlphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb055AlphaDummy003 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_010`. -/
@[expose]
noncomputable def nb055AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy006)
            (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_011`. -/
@[expose]
noncomputable def nb055AlphaDummy011 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_012`. -/
@[expose]
noncomputable def nb055AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
            (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
            (Wff.classEq (Class.cv (nb055AlphaDummy006))
              (synCphi (Class.cv (nb055AlphaDummy007))))))).fv ∪
      ((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
            (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
            (Wff.classEq (Class.cv (nb055AlphaDummy006))
              (synCphi (Class.cv (nb055AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_013`. -/
@[expose]
noncomputable def nb055AlphaDummy013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy008 x y)
          (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
              (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv ∪
      ((Class.cab (nb055AlphaDummy008 x y)
          (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
              (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_014`. -/
@[expose]
noncomputable def nb055AlphaDummy014 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_015`. -/
@[expose]
noncomputable def nb055AlphaDummy015 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_016`. -/
@[expose]
noncomputable def nb055AlphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_017`. -/
@[expose]
noncomputable def nb055AlphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_018`. -/
@[expose]
noncomputable def nb055AlphaDummy018 : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCphi (Class.cv (nb055AlphaDummy015)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_019`. -/
@[expose]
noncomputable def nb055AlphaDummy019 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCphi (Class.cv (nb055AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_020`. -/
@[expose]
noncomputable def nb055AlphaDummy020 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy014)
          (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
            (Wff.classEq (Class.cv (nb055AlphaDummy014))
              (synCphi (Class.cv (nb055AlphaDummy015))))))).fv ∪
      ((Class.cab (nb055AlphaDummy014)
          (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
            (Wff.classEq (Class.cv (nb055AlphaDummy014))
              (synCphi (Class.cv (nb055AlphaDummy015))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_021`. -/
@[expose]
noncomputable def nb055AlphaDummy021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy016 x y)
          (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
              (synCphi (Class.cv (nb055AlphaDummy017 x y))))))).fv ∪
      ((Class.cab (nb055AlphaDummy016 x y) (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
              (synCphi (Class.cv (nb055AlphaDummy017 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_022`. -/
@[expose]
noncomputable def nb055AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_023`. -/
@[expose]
noncomputable def nb055AlphaDummy023 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy015))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_024`. -/
@[expose]
noncomputable def nb055AlphaDummy024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_025`. -/
@[expose]
noncomputable def nb055AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy017 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_026`. -/
@[expose]
noncomputable def nb055AlphaDummy026 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy022)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy022)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_027`. -/
@[expose]
noncomputable def nb055AlphaDummy027 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy024 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy024 x y)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy024 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_028`. -/
@[expose]
noncomputable def nb055AlphaDummy028 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_029`. -/
@[expose]
noncomputable def nb055AlphaDummy029 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_030`. -/
@[expose]
noncomputable def nb055AlphaDummy030 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_031`. -/
@[expose]
noncomputable def nb055AlphaDummy031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_032`. -/
@[expose]
noncomputable def nb055AlphaDummy032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_033`. -/
@[expose]
noncomputable def nb055AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_034`. -/
@[expose]
noncomputable def nb055AlphaDummy034 : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy029))
          (Class.cv (nb055AlphaDummy030)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_035`. -/
@[expose]
noncomputable def nb055AlphaDummy035 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy032 x y))
          (Class.cv (nb055AlphaDummy033 x y)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy032 x y))
          (Class.cv (nb055AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_036`. -/
@[expose]
noncomputable def nb055AlphaDummy036 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_037`. -/
@[expose]
noncomputable def nb055AlphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_038`. -/
@[expose]
noncomputable def nb055AlphaDummy038 : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy029)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_039`. -/
@[expose]
noncomputable def nb055AlphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy032 x y)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_040`. -/
@[expose]
noncomputable def nb055AlphaDummy040 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy029))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_041`. -/
@[expose]
noncomputable def nb055AlphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy032 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_042`. -/
@[expose]
noncomputable def nb055AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy030))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_043`. -/
@[expose]
noncomputable def nb055AlphaDummy043 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy033 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_044`. -/
@[expose]
noncomputable def nb055AlphaDummy044 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy014)
          (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
            (Wff.classEq (Class.cv (nb055AlphaDummy014))
              (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy014)
          (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
            (Wff.classEq (Class.cv (nb055AlphaDummy014))
              (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_045`. -/
@[expose]
noncomputable def nb055AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy016 x y)
          (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy016 x y)
          (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_046`. -/
@[expose]
noncomputable def nb055AlphaDummy046 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy015))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_047`. -/
@[expose]
noncomputable def nb055AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy017 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_048`. -/
@[expose]
noncomputable def nb055AlphaDummy048 : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy015)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy015)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_049`. -/
@[expose]
noncomputable def nb055AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy017 x y)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy017 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_050`. -/
@[expose]
noncomputable def nb055AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_051`. -/
@[expose]
noncomputable def nb055AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_052`. -/
@[expose]
noncomputable def nb055AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy009 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_053`. -/
@[expose]
noncomputable def nb055AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy009 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_054`. -/
@[expose]
noncomputable def nb055AlphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy050)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy050)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_055`. -/
@[expose]
noncomputable def nb055AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_056`. -/
@[expose]
noncomputable def nb055AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_057`. -/
@[expose]
noncomputable def nb055AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_058`. -/
@[expose]
noncomputable def nb055AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_059`. -/
@[expose]
noncomputable def nb055AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_060`. -/
@[expose]
noncomputable def nb055AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_061`. -/
@[expose]
noncomputable def nb055AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_062`. -/
@[expose]
noncomputable def nb055AlphaDummy062 : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy057))
          (Class.cv (nb055AlphaDummy058)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_063`. -/
@[expose]
noncomputable def nb055AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy060 x y))
          (Class.cv (nb055AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy060 x y))
          (Class.cv (nb055AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_064`. -/
@[expose]
noncomputable def nb055AlphaDummy064 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_065`. -/
@[expose]
noncomputable def nb055AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_066`. -/
@[expose]
noncomputable def nb055AlphaDummy066 : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy057)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_067`. -/
@[expose]
noncomputable def nb055AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_068`. -/
@[expose]
noncomputable def nb055AlphaDummy068 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_069`. -/
@[expose]
noncomputable def nb055AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_070`. -/
@[expose]
noncomputable def nb055AlphaDummy070 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy058))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_071`. -/
@[expose]
noncomputable def nb055AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_072`. -/
@[expose]
noncomputable def nb055AlphaDummy072 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy006)
          (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
            (Wff.classEq (Class.cv (nb055AlphaDummy006))
              (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy006)
          (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
            (Wff.classEq (Class.cv (nb055AlphaDummy006))
              (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_073`. -/
@[expose]
noncomputable def nb055AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy008 x y)
          (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy008 x y)
          (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_074`. -/
@[expose]
noncomputable def nb055AlphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_075`. -/
@[expose]
noncomputable def nb055AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy009 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_076`. -/
@[expose]
noncomputable def nb055AlphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_077`. -/
@[expose]
noncomputable def nb055AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy009 x y)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy009 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_078`. -/
@[expose]
noncomputable def nb055AlphaDummy078 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_079`. -/
@[expose]
noncomputable def nb055AlphaDummy079 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_080`. -/
@[expose]
noncomputable def nb055AlphaDummy080 : Var :=
  (freshVar
    (({(nb055AlphaDummy014)} : Finset Var) ∪ ({(nb055AlphaDummy015)} : Finset Var) ∪
      ((synWex (nb055AlphaDummy078) (synWa
            (synWbr (Class.cv (nb055AlphaDummy014)) (Class.cv (nb055AlphaDummy001))
              (Class.cv (nb055AlphaDummy078)))
            (synWbr (Class.cv (nb055AlphaDummy078)) (Class.cv (nb055AlphaDummy000))
              (Class.cv (nb055AlphaDummy015)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_081`. -/
@[expose]
noncomputable def nb055AlphaDummy081 (x : Var) (y : Var) : Var :=
  (freshVar (({(nb055AlphaDummy016 x y)} : Finset Var) ∪
        ({(nb055AlphaDummy017 x y)} : Finset Var) ∪ ((synWex (nb055AlphaDummy079 x y)
          (synWa (synWbr (Class.cv (nb055AlphaDummy016 x y)) (Class.cv y)
              (Class.cv (nb055AlphaDummy079 x y)))
            (synWbr (Class.cv (nb055AlphaDummy079 x y)) (Class.cv x)
              (Class.cv (nb055AlphaDummy017 x y)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_082`. -/
@[expose]
noncomputable def nb055AlphaDummy082 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_083`. -/
@[expose]
noncomputable def nb055AlphaDummy083 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_084`. -/
@[expose]
noncomputable def nb055AlphaDummy084 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_085`. -/
@[expose]
noncomputable def nb055AlphaDummy085 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy017 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_086`. -/
@[expose]
noncomputable def nb055AlphaDummy086 : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCphi (Class.cv (nb055AlphaDummy083)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_087`. -/
@[expose]
noncomputable def nb055AlphaDummy087 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCphi (Class.cv (nb055AlphaDummy085 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_088`. -/
@[expose]
noncomputable def nb055AlphaDummy088 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy082)
          (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
            (Wff.classEq (Class.cv (nb055AlphaDummy082))
              (synCphi (Class.cv (nb055AlphaDummy083))))))).fv ∪
      ((Class.cab (nb055AlphaDummy082)
          (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
            (Wff.classEq (Class.cv (nb055AlphaDummy082))
              (synCphi (Class.cv (nb055AlphaDummy083))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_089`. -/
@[expose]
noncomputable def nb055AlphaDummy089 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy084 x y)
          (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
              (synCphi (Class.cv (nb055AlphaDummy085 x y))))))).fv ∪
      ((Class.cab (nb055AlphaDummy084 x y)
          (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
              (synCphi (Class.cv (nb055AlphaDummy085 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_090`. -/
@[expose]
noncomputable def nb055AlphaDummy090 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy083))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_091`. -/
@[expose]
noncomputable def nb055AlphaDummy091 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy083))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_092`. -/
@[expose]
noncomputable def nb055AlphaDummy092 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy085 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_093`. -/
@[expose]
noncomputable def nb055AlphaDummy093 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy085 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_094`. -/
@[expose]
noncomputable def nb055AlphaDummy094 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy090)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy090)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy090))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_095`. -/
@[expose]
noncomputable def nb055AlphaDummy095 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy092 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy092 x y)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy092 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_096`. -/
@[expose]
noncomputable def nb055AlphaDummy096 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_097`. -/
@[expose]
noncomputable def nb055AlphaDummy097 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_098`. -/
@[expose]
noncomputable def nb055AlphaDummy098 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_099`. -/
@[expose]
noncomputable def nb055AlphaDummy099 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_100`. -/
@[expose]
noncomputable def nb055AlphaDummy100 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_101`. -/
@[expose]
noncomputable def nb055AlphaDummy101 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_102`. -/
@[expose]
noncomputable def nb055AlphaDummy102 : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy097))
          (Class.cv (nb055AlphaDummy098)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_103`. -/
@[expose]
noncomputable def nb055AlphaDummy103 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy100 x y))
          (Class.cv (nb055AlphaDummy101 x y)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy100 x y))
          (Class.cv (nb055AlphaDummy101 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_104`. -/
@[expose]
noncomputable def nb055AlphaDummy104 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_105`. -/
@[expose]
noncomputable def nb055AlphaDummy105 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy101 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_106`. -/
@[expose]
noncomputable def nb055AlphaDummy106 : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy097)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy098)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_107`. -/
@[expose]
noncomputable def nb055AlphaDummy107 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy100 x y)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy101 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_108`. -/
@[expose]
noncomputable def nb055AlphaDummy108 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy097))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_109`. -/
@[expose]
noncomputable def nb055AlphaDummy109 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy100 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_110`. -/
@[expose]
noncomputable def nb055AlphaDummy110 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy098))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_111`. -/
@[expose]
noncomputable def nb055AlphaDummy111 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy101 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy101 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_112`. -/
@[expose]
noncomputable def nb055AlphaDummy112 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy082)
          (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
            (Wff.classEq (Class.cv (nb055AlphaDummy082))
              (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy082)
          (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
            (Wff.classEq (Class.cv (nb055AlphaDummy082))
              (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_113`. -/
@[expose]
noncomputable def nb055AlphaDummy113 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy084 x y)
          (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy084 x y)
          (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_114`. -/
@[expose]
noncomputable def nb055AlphaDummy114 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy083))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_115`. -/
@[expose]
noncomputable def nb055AlphaDummy115 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy085 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_116`. -/
@[expose]
noncomputable def nb055AlphaDummy116 : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy083)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy083)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_117`. -/
@[expose]
noncomputable def nb055AlphaDummy117 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy085 x y)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy085 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_118`. -/
@[expose]
noncomputable def nb055AlphaDummy118 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_119`. -/
@[expose]
noncomputable def nb055AlphaDummy119 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_120`. -/
@[expose]
noncomputable def nb055AlphaDummy120 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy079 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_121`. -/
@[expose]
noncomputable def nb055AlphaDummy121 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy079 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_122`. -/
@[expose]
noncomputable def nb055AlphaDummy122 : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCphi (Class.cv (nb055AlphaDummy119)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_123`. -/
@[expose]
noncomputable def nb055AlphaDummy123 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCphi (Class.cv (nb055AlphaDummy121 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_124`. -/
@[expose]
noncomputable def nb055AlphaDummy124 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy118)
          (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
            (Wff.classEq (Class.cv (nb055AlphaDummy118))
              (synCphi (Class.cv (nb055AlphaDummy119))))))).fv ∪
      ((Class.cab (nb055AlphaDummy118)
          (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
            (Wff.classEq (Class.cv (nb055AlphaDummy118))
              (synCphi (Class.cv (nb055AlphaDummy119))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_125`. -/
@[expose]
noncomputable def nb055AlphaDummy125 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy120 x y)
          (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
              (synCphi (Class.cv (nb055AlphaDummy121 x y))))))).fv ∪
      ((Class.cab (nb055AlphaDummy120 x y)
          (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
              (synCphi (Class.cv (nb055AlphaDummy121 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_126`. -/
@[expose]
noncomputable def nb055AlphaDummy126 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy119))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_127`. -/
@[expose]
noncomputable def nb055AlphaDummy127 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy119))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_128`. -/
@[expose]
noncomputable def nb055AlphaDummy128 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy121 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_129`. -/
@[expose]
noncomputable def nb055AlphaDummy129 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy121 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_130`. -/
@[expose]
noncomputable def nb055AlphaDummy130 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy126)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy126)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy126))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_131`. -/
@[expose]
noncomputable def nb055AlphaDummy131 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy128 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy128 x y)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy128 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_132`. -/
@[expose]
noncomputable def nb055AlphaDummy132 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_133`. -/
@[expose]
noncomputable def nb055AlphaDummy133 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_134`. -/
@[expose]
noncomputable def nb055AlphaDummy134 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_135`. -/
@[expose]
noncomputable def nb055AlphaDummy135 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_136`. -/
@[expose]
noncomputable def nb055AlphaDummy136 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_137`. -/
@[expose]
noncomputable def nb055AlphaDummy137 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_138`. -/
@[expose]
noncomputable def nb055AlphaDummy138 : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy133))
          (Class.cv (nb055AlphaDummy134)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_139`. -/
@[expose]
noncomputable def nb055AlphaDummy139 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy136 x y))
          (Class.cv (nb055AlphaDummy137 x y)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy136 x y))
          (Class.cv (nb055AlphaDummy137 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_140`. -/
@[expose]
noncomputable def nb055AlphaDummy140 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_141`. -/
@[expose]
noncomputable def nb055AlphaDummy141 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy137 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_142`. -/
@[expose]
noncomputable def nb055AlphaDummy142 : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy133)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy134)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_143`. -/
@[expose]
noncomputable def nb055AlphaDummy143 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy136 x y)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy137 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_144`. -/
@[expose]
noncomputable def nb055AlphaDummy144 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy133))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_145`. -/
@[expose]
noncomputable def nb055AlphaDummy145 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy136 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_146`. -/
@[expose]
noncomputable def nb055AlphaDummy146 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy134))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_147`. -/
@[expose]
noncomputable def nb055AlphaDummy147 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy137 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy137 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_148`. -/
@[expose]
noncomputable def nb055AlphaDummy148 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy118)
          (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
            (Wff.classEq (Class.cv (nb055AlphaDummy118))
              (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy118)
          (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
            (Wff.classEq (Class.cv (nb055AlphaDummy118))
              (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_149`. -/
@[expose]
noncomputable def nb055AlphaDummy149 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy120 x y)
          (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy120 x y)
          (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                (synCsn (synC0c))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_150`. -/
@[expose]
noncomputable def nb055AlphaDummy150 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy119))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_151`. -/
@[expose]
noncomputable def nb055AlphaDummy151 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy121 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_152`. -/
@[expose]
noncomputable def nb055AlphaDummy152 : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy119)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy119)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_153`. -/
@[expose]
noncomputable def nb055AlphaDummy153 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy121 x y)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy121 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_154`. -/
@[expose]
noncomputable def nb055AlphaDummy154 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_155`. -/
@[expose]
noncomputable def nb055AlphaDummy155 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_156`. -/
@[expose]
noncomputable def nb055AlphaDummy156 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_157`. -/
@[expose]
noncomputable def nb055AlphaDummy157 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy017 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_158`. -/
@[expose]
noncomputable def nb055AlphaDummy158 : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCphi (Class.cv (nb055AlphaDummy155)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_159`. -/
@[expose]
noncomputable def nb055AlphaDummy159 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCphi (Class.cv (nb055AlphaDummy157 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_160`. -/
@[expose]
noncomputable def nb055AlphaDummy160 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy154)
          (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
            (Wff.classEq (Class.cv (nb055AlphaDummy154))
              (synCphi (Class.cv (nb055AlphaDummy155))))))).fv ∪
      ((Class.cab (nb055AlphaDummy154)
          (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
            (Wff.classEq (Class.cv (nb055AlphaDummy154))
              (synCphi (Class.cv (nb055AlphaDummy155))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_161`. -/
@[expose]
noncomputable def nb055AlphaDummy161 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy156 x y)
          (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
              (synCphi (Class.cv (nb055AlphaDummy157 x y))))))).fv ∪
      ((Class.cab (nb055AlphaDummy156 x y)
          (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
              (synCphi (Class.cv (nb055AlphaDummy157 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_162`. -/
@[expose]
noncomputable def nb055AlphaDummy162 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy155))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_163`. -/
@[expose]
noncomputable def nb055AlphaDummy163 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy155))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_164`. -/
@[expose]
noncomputable def nb055AlphaDummy164 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy157 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_165`. -/
@[expose]
noncomputable def nb055AlphaDummy165 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy157 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_166`. -/
@[expose]
noncomputable def nb055AlphaDummy166 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy162)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy162)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy162))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_167`. -/
@[expose]
noncomputable def nb055AlphaDummy167 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb055AlphaDummy164 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb055AlphaDummy164 x y)) (synC1c))).fv ∪
      ((Class.cv (nb055AlphaDummy164 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_168`. -/
@[expose]
noncomputable def nb055AlphaDummy168 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_169`. -/
@[expose]
noncomputable def nb055AlphaDummy169 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_170`. -/
@[expose]
noncomputable def nb055AlphaDummy170 : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_171`. -/
@[expose]
noncomputable def nb055AlphaDummy171 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_172`. -/
@[expose]
noncomputable def nb055AlphaDummy172 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_173`. -/
@[expose]
noncomputable def nb055AlphaDummy173 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_174`. -/
@[expose]
noncomputable def nb055AlphaDummy174 : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy169))
          (Class.cv (nb055AlphaDummy170)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_175`. -/
@[expose]
noncomputable def nb055AlphaDummy175 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb055AlphaDummy172 x y))
          (Class.cv (nb055AlphaDummy173 x y)))).fv ∪
      ((synCnin (Class.cv (nb055AlphaDummy172 x y))
          (Class.cv (nb055AlphaDummy173 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_176`. -/
@[expose]
noncomputable def nb055AlphaDummy176 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_177`. -/
@[expose]
noncomputable def nb055AlphaDummy177 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy173 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_178`. -/
@[expose]
noncomputable def nb055AlphaDummy178 : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy169)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy170)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_179`. -/
@[expose]
noncomputable def nb055AlphaDummy179 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb055AlphaDummy172 x y)))).fv ∪
      ((synCcompl (Class.cv (nb055AlphaDummy173 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_180`. -/
@[expose]
noncomputable def nb055AlphaDummy180 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy169))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_181`. -/
@[expose]
noncomputable def nb055AlphaDummy181 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy172 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_182`. -/
@[expose]
noncomputable def nb055AlphaDummy182 : Var :=
  (freshVar
    (((Class.cv (nb055AlphaDummy170))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_183`. -/
@[expose]
noncomputable def nb055AlphaDummy183 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb055AlphaDummy173 x y))).fv ∪
      ((Class.cv (nb055AlphaDummy173 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_184`. -/
@[expose]
noncomputable def nb055AlphaDummy184 : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy154)
          (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
            (Wff.classEq (Class.cv (nb055AlphaDummy154))
              (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy154)
          (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
            (Wff.classEq (Class.cv (nb055AlphaDummy154))
              (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_185`. -/
@[expose]
noncomputable def nb055AlphaDummy185 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb055AlphaDummy156 x y)
          (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy156 x y)
          (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
            (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
              (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_186`. -/
@[expose]
noncomputable def nb055AlphaDummy186 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy155))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_187`. -/
@[expose]
noncomputable def nb055AlphaDummy187 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb055AlphaDummy157 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_188`. -/
@[expose]
noncomputable def nb055AlphaDummy188 : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy155)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy155)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb055_alpha_dummy_189`. -/
@[expose]
noncomputable def nb055AlphaDummy189 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb055AlphaDummy157 x y)))).fv ∪
      ((synCphi (Class.cv (nb055AlphaDummy157 x y)))).fv) 0)

theorem nb055_fresh_000 :
    (nb055AlphaDummy072) ∉
      (((Class.cab (nb055AlphaDummy006)
            (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy006)
            (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy006)
            (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy006)
            (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_001 :
    (nb055AlphaDummy012) ∉
      (((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007))))))).fv ∪
        ((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007))))))).fv) :=
  by
  simpa only [nb055AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007))))))).fv ∪
        ((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007))))))).fv)
      0

theorem nb055_fresh_002 (x : Var) (y : Var) :
    (nb055AlphaDummy073 x y) ∉
      (((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_003 (x : Var) (y : Var) :
    (nb055AlphaDummy013 x y) ∉
      (((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv) :=
  by
  simpa only [nb055AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv)
      0

theorem nb055_fresh_004 :
    (nb055AlphaDummy020) ∉
      (((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCphi (Class.cv (nb055AlphaDummy015))))))).fv ∪
        ((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCphi (Class.cv (nb055AlphaDummy015))))))).fv) :=
  by
  simpa only [nb055AlphaDummy020] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCphi (Class.cv (nb055AlphaDummy015))))))).fv ∪
        ((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCphi (Class.cv (nb055AlphaDummy015))))))).fv)
      0

theorem nb055_fresh_005 :
    (nb055AlphaDummy044) ∉
      (((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy044] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_006 (x : Var) (y : Var) :
    (nb055AlphaDummy021 x y) ∉
      (((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCphi (Class.cv (nb055AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCphi (Class.cv (nb055AlphaDummy017 x y))))))).fv) :=
  by
  simpa only [nb055AlphaDummy021] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCphi (Class.cv (nb055AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCphi (Class.cv (nb055AlphaDummy017 x y))))))).fv)
      0

theorem nb055_fresh_007 (x : Var) (y : Var) :
    (nb055AlphaDummy045 x y) ∉
      (((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy045] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_008 :
    (nb055AlphaDummy088) ∉
      (((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCphi (Class.cv (nb055AlphaDummy083))))))).fv ∪
        ((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCphi (Class.cv (nb055AlphaDummy083))))))).fv) :=
  by
  simpa only [nb055AlphaDummy088] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCphi (Class.cv (nb055AlphaDummy083))))))).fv ∪
        ((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCphi (Class.cv (nb055AlphaDummy083))))))).fv)
      0

theorem nb055_fresh_009 :
    (nb055AlphaDummy112) ∉
      (((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy112] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_010 (x : Var) (y : Var) :
    (nb055AlphaDummy089 x y) ∉
      (((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCphi (Class.cv (nb055AlphaDummy085 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCphi (Class.cv (nb055AlphaDummy085 x y))))))).fv) :=
  by
  simpa only [nb055AlphaDummy089] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCphi (Class.cv (nb055AlphaDummy085 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCphi (Class.cv (nb055AlphaDummy085 x y))))))).fv)
      0

theorem nb055_fresh_011 (x : Var) (y : Var) :
    (nb055AlphaDummy113 x y) ∉
      (((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy113] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_012 :
    (nb055AlphaDummy124) ∉
      (((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCphi (Class.cv (nb055AlphaDummy119))))))).fv ∪
        ((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCphi (Class.cv (nb055AlphaDummy119))))))).fv) :=
  by
  simpa only [nb055AlphaDummy124] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCphi (Class.cv (nb055AlphaDummy119))))))).fv ∪
        ((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCphi (Class.cv (nb055AlphaDummy119))))))).fv)
      0

theorem nb055_fresh_013 :
    (nb055AlphaDummy148) ∉
      (((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy148] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_014 (x : Var) (y : Var) :
    (nb055AlphaDummy125 x y) ∉
      (((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCphi (Class.cv (nb055AlphaDummy121 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCphi (Class.cv (nb055AlphaDummy121 x y))))))).fv) :=
  by
  simpa only [nb055AlphaDummy125] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCphi (Class.cv (nb055AlphaDummy121 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCphi (Class.cv (nb055AlphaDummy121 x y))))))).fv)
      0

theorem nb055_fresh_015 (x : Var) (y : Var) :
    (nb055AlphaDummy149 x y) ∉
      (((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy149] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_016 :
    (nb055AlphaDummy184) ∉
      (((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy184] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_017 :
    (nb055AlphaDummy160) ∉
      (((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCphi (Class.cv (nb055AlphaDummy155))))))).fv ∪
        ((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCphi (Class.cv (nb055AlphaDummy155))))))).fv) :=
  by
  simpa only [nb055AlphaDummy160] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCphi (Class.cv (nb055AlphaDummy155))))))).fv ∪
        ((Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCphi (Class.cv (nb055AlphaDummy155))))))).fv)
      0

theorem nb055_fresh_018 (x : Var) (y : Var) :
    (nb055AlphaDummy185 x y) ∉
      (((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb055AlphaDummy185] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb055_fresh_019 (x : Var) (y : Var) :
    (nb055AlphaDummy161 x y) ∉
      (((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCphi (Class.cv (nb055AlphaDummy157 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCphi (Class.cv (nb055AlphaDummy157 x y))))))).fv) :=
  by
  simpa only [nb055AlphaDummy161] using
    freshVar_not_mem
      (((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCphi (Class.cv (nb055AlphaDummy157 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCphi (Class.cv (nb055AlphaDummy157 x y))))))).fv)
      0

theorem nb055_fresh_020 :
    (nb055AlphaDummy014) ∉
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) :=
  by
  simpa only [nb055AlphaDummy014] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
      0

theorem nb055_fresh_021 :
    (nb055AlphaDummy015) ∉
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) :=
  by
  simpa only [nb055AlphaDummy015] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
      1

theorem nb055_fresh_022 :
    (nb055AlphaDummy078) ∉
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) :=
  by
  simpa only [nb055AlphaDummy078] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
      2

theorem nb055_distinct_023 : (nb055AlphaDummy014) ≠ (nb055AlphaDummy015) := by
  simpa only [nb055AlphaDummy014, nb055AlphaDummy015] using
    (freshVar_injective
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_024 : (nb055AlphaDummy014) ≠ (nb055AlphaDummy078) := by
  simpa only [nb055AlphaDummy014, nb055AlphaDummy078] using
    (freshVar_injective
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_025 : (nb055AlphaDummy015) ≠ (nb055AlphaDummy078) := by
  simpa only [nb055AlphaDummy015, nb055AlphaDummy078] using
    (freshVar_injective
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_026 :
    (nb055AlphaDummy050) ∉ (((Class.cv (nb055AlphaDummy007))).fv) := by
  simpa only [nb055AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy007))).fv) 0

theorem nb055_fresh_027 :
    (nb055AlphaDummy051) ∉ (((Class.cv (nb055AlphaDummy007))).fv) := by
  simpa only [nb055AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy007))).fv) 1

theorem nb055_distinct_028 : (nb055AlphaDummy050) ≠ (nb055AlphaDummy051) := by
  simpa only [nb055AlphaDummy050, nb055AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_029 (x : Var) (y : Var) :
    (nb055AlphaDummy052 x y) ∉ (((Class.cv (nb055AlphaDummy009 x y))).fv) := by
  simpa only [nb055AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy009 x y))).fv) 0

theorem nb055_fresh_030 (x : Var) (y : Var) :
    (nb055AlphaDummy053 x y) ∉ (((Class.cv (nb055AlphaDummy009 x y))).fv) := by
  simpa only [nb055AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy009 x y))).fv) 1

theorem nb055_distinct_031 (x : Var) (y : Var) :
    (nb055AlphaDummy052 x y) ≠ (nb055AlphaDummy053 x y) := by
  simpa only [nb055AlphaDummy052, nb055AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy009 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_032 :
    (nb055AlphaDummy082) ∉
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  simpa only [nb055AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv)
      0

theorem nb055_fresh_033 :
    (nb055AlphaDummy083) ∉
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  simpa only [nb055AlphaDummy083] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv)
      1

theorem nb055_distinct_034 : (nb055AlphaDummy082) ≠ (nb055AlphaDummy083) := by
  simpa only [nb055AlphaDummy082, nb055AlphaDummy083] using
    (freshVar_injective
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_fresh_035 :
    (nb055AlphaDummy118) ∉
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv) :=
  by
  simpa only [nb055AlphaDummy118] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv)
      0

theorem nb055_fresh_036 :
    (nb055AlphaDummy119) ∉
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv) :=
  by
  simpa only [nb055AlphaDummy119] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv)
      1

theorem nb055_distinct_037 : (nb055AlphaDummy118) ≠ (nb055AlphaDummy119) := by
  simpa only [nb055AlphaDummy118, nb055AlphaDummy119] using
    (freshVar_injective
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_fresh_038 :
    (nb055AlphaDummy022) ∉ (((Class.cv (nb055AlphaDummy015))).fv) := by
  simpa only [nb055AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy015))).fv) 0

theorem nb055_fresh_039 :
    (nb055AlphaDummy023) ∉ (((Class.cv (nb055AlphaDummy015))).fv) := by
  simpa only [nb055AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy015))).fv) 1

theorem nb055_distinct_040 : (nb055AlphaDummy022) ≠ (nb055AlphaDummy023) := by
  simpa only [nb055AlphaDummy022, nb055AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy015))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_041 (x : Var) (y : Var) :
    (nb055AlphaDummy084 x y) ∉
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy084] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv)
      0

theorem nb055_fresh_042 (x : Var) (y : Var) :
    (nb055AlphaDummy085 x y) ∉
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy085] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv)
      1

theorem nb055_distinct_043 (x : Var) (y : Var) :
    (nb055AlphaDummy084 x y) ≠ (nb055AlphaDummy085 x y) := by
  simpa only [nb055AlphaDummy084, nb055AlphaDummy085] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_044 (x : Var) (y : Var) :
    (nb055AlphaDummy120 x y) ∉
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy079 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy120] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy079 x y))).fv)
      0

theorem nb055_fresh_045 (x : Var) (y : Var) :
    (nb055AlphaDummy121 x y) ∉
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy079 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy121] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy079 x y))).fv)
      1

theorem nb055_distinct_046 (x : Var) (y : Var) :
    (nb055AlphaDummy120 x y) ≠ (nb055AlphaDummy121 x y) := by
  simpa only [nb055AlphaDummy120, nb055AlphaDummy121] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy079 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_047 (x : Var) (y : Var) :
    (nb055AlphaDummy024 x y) ∉ (((Class.cv (nb055AlphaDummy017 x y))).fv) := by
  simpa only [nb055AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy017 x y))).fv) 0

theorem nb055_fresh_048 (x : Var) (y : Var) :
    (nb055AlphaDummy025 x y) ∉ (((Class.cv (nb055AlphaDummy017 x y))).fv) := by
  simpa only [nb055AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy017 x y))).fv) 1

theorem nb055_distinct_049 (x : Var) (y : Var) :
    (nb055AlphaDummy024 x y) ≠ (nb055AlphaDummy025 x y) := by
  simpa only [nb055AlphaDummy024, nb055AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy017 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_050 :
    (nb055AlphaDummy028) ∉
      (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_051 :
    (nb055AlphaDummy029) ∉
      (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_052 :
    (nb055AlphaDummy030) ∉
      (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_053 : (nb055AlphaDummy028) ≠ (nb055AlphaDummy029) := by
  simpa only [nb055AlphaDummy028, nb055AlphaDummy029] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_054 : (nb055AlphaDummy028) ≠ (nb055AlphaDummy030) := by
  simpa only [nb055AlphaDummy028, nb055AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_055 : (nb055AlphaDummy029) ≠ (nb055AlphaDummy030) := by
  simpa only [nb055AlphaDummy029, nb055AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_056 (x : Var) (y : Var) :
    (nb055AlphaDummy031 x y) ∉
      (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_057 (x : Var) (y : Var) :
    (nb055AlphaDummy032 x y) ∉
      (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_058 (x : Var) (y : Var) :
    (nb055AlphaDummy033 x y) ∉
      (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_059 (x : Var) (y : Var) :
    (nb055AlphaDummy031 x y) ≠ (nb055AlphaDummy032 x y) := by
  simpa only [nb055AlphaDummy031, nb055AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_060 (x : Var) (y : Var) :
    (nb055AlphaDummy031 x y) ≠ (nb055AlphaDummy033 x y) := by
  simpa only [nb055AlphaDummy031, nb055AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_061 (x : Var) (y : Var) :
    (nb055AlphaDummy032 x y) ≠ (nb055AlphaDummy033 x y) := by
  simpa only [nb055AlphaDummy032, nb055AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_062 :
    (nb055AlphaDummy040) ∉
      (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy029))).fv) :=
  by
  simpa only [nb055AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy029))).fv)
      0

theorem nb055_fresh_063 :
    (nb055AlphaDummy036) ∉
      (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv) :=
  by
  simpa only [nb055AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv)
      0

theorem nb055_fresh_064 :
    (nb055AlphaDummy042) ∉
      (((Class.cv (nb055AlphaDummy030))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv) :=
  by
  simpa only [nb055AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy030))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv)
      0

theorem nb055_fresh_065 (x : Var) (y : Var) :
    (nb055AlphaDummy041 x y) ∉
      (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy032 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy032 x y))).fv)
      0

theorem nb055_fresh_066 (x : Var) (y : Var) :
    (nb055AlphaDummy037 x y) ∉
      (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy033 x y))).fv)
      0

theorem nb055_fresh_067 (x : Var) (y : Var) :
    (nb055AlphaDummy043 x y) ∉
      (((Class.cv (nb055AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy033 x y))).fv)
      0

theorem nb055_fresh_068 :
    (nb055AlphaDummy056) ∉
      (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_069 :
    (nb055AlphaDummy057) ∉
      (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_070 :
    (nb055AlphaDummy058) ∉
      (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_071 : (nb055AlphaDummy056) ≠ (nb055AlphaDummy057) := by
  simpa only [nb055AlphaDummy056, nb055AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_072 : (nb055AlphaDummy056) ≠ (nb055AlphaDummy058) := by
  simpa only [nb055AlphaDummy056, nb055AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_073 : (nb055AlphaDummy057) ≠ (nb055AlphaDummy058) := by
  simpa only [nb055AlphaDummy057, nb055AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_074 (x : Var) (y : Var) :
    (nb055AlphaDummy059 x y) ∉
      (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_075 (x : Var) (y : Var) :
    (nb055AlphaDummy060 x y) ∉
      (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_076 (x : Var) (y : Var) :
    (nb055AlphaDummy061 x y) ∉
      (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_077 (x : Var) (y : Var) :
    (nb055AlphaDummy059 x y) ≠ (nb055AlphaDummy060 x y) := by
  simpa only [nb055AlphaDummy059, nb055AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_078 (x : Var) (y : Var) :
    (nb055AlphaDummy059 x y) ≠ (nb055AlphaDummy061 x y) := by
  simpa only [nb055AlphaDummy059, nb055AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_079 (x : Var) (y : Var) :
    (nb055AlphaDummy060 x y) ≠ (nb055AlphaDummy061 x y) := by
  simpa only [nb055AlphaDummy060, nb055AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_080 :
    (nb055AlphaDummy068) ∉
      (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy057))).fv) :=
  by
  simpa only [nb055AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy057))).fv)
      0

theorem nb055_fresh_081 :
    (nb055AlphaDummy064) ∉
      (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv) :=
  by
  simpa only [nb055AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv)
      0

theorem nb055_fresh_082 :
    (nb055AlphaDummy070) ∉
      (((Class.cv (nb055AlphaDummy058))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv) :=
  by
  simpa only [nb055AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy058))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv)
      0

theorem nb055_fresh_083 (x : Var) (y : Var) :
    (nb055AlphaDummy069 x y) ∉
      (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy060 x y))).fv)
      0

theorem nb055_fresh_084 (x : Var) (y : Var) :
    (nb055AlphaDummy065 x y) ∉
      (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy061 x y))).fv)
      0

theorem nb055_fresh_085 (x : Var) (y : Var) :
    (nb055AlphaDummy071 x y) ∉
      (((Class.cv (nb055AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy061 x y))).fv)
      0

theorem nb055_fresh_086 :
    (nb055AlphaDummy154) ∉
      (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  simpa only [nb055AlphaDummy154] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv)
      0

theorem nb055_fresh_087 :
    (nb055AlphaDummy155) ∉
      (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  simpa only [nb055AlphaDummy155] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv)
      1

theorem nb055_distinct_088 : (nb055AlphaDummy154) ≠ (nb055AlphaDummy155) := by
  simpa only [nb055AlphaDummy154, nb055AlphaDummy155] using
    (freshVar_injective
      (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_fresh_089 (x : Var) (y : Var) :
    (nb055AlphaDummy156 x y) ∉
      (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy156] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv)
      0

theorem nb055_fresh_090 (x : Var) (y : Var) :
    (nb055AlphaDummy157 x y) ∉
      (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy157] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv)
      1

theorem nb055_distinct_091 (x : Var) (y : Var) :
    (nb055AlphaDummy156 x y) ≠ (nb055AlphaDummy157 x y) := by
  simpa only [nb055AlphaDummy156, nb055AlphaDummy157] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_092 :
    (nb055AlphaDummy090) ∉ (((Class.cv (nb055AlphaDummy083))).fv) := by
  simpa only [nb055AlphaDummy090] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy083))).fv) 0

theorem nb055_fresh_093 :
    (nb055AlphaDummy091) ∉ (((Class.cv (nb055AlphaDummy083))).fv) := by
  simpa only [nb055AlphaDummy091] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy083))).fv) 1

theorem nb055_distinct_094 : (nb055AlphaDummy090) ≠ (nb055AlphaDummy091) := by
  simpa only [nb055AlphaDummy090, nb055AlphaDummy091] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy083))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_095 (x : Var) (y : Var) :
    (nb055AlphaDummy092 x y) ∉ (((Class.cv (nb055AlphaDummy085 x y))).fv) := by
  simpa only [nb055AlphaDummy092] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy085 x y))).fv) 0

theorem nb055_fresh_096 (x : Var) (y : Var) :
    (nb055AlphaDummy093 x y) ∉ (((Class.cv (nb055AlphaDummy085 x y))).fv) := by
  simpa only [nb055AlphaDummy093] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy085 x y))).fv) 1

theorem nb055_distinct_097 (x : Var) (y : Var) :
    (nb055AlphaDummy092 x y) ≠ (nb055AlphaDummy093 x y) := by
  simpa only [nb055AlphaDummy092, nb055AlphaDummy093] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy085 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_098 :
    (nb055AlphaDummy096) ∉
      (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_099 :
    (nb055AlphaDummy097) ∉
      (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_100 :
    (nb055AlphaDummy098) ∉
      (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy098] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_101 : (nb055AlphaDummy096) ≠ (nb055AlphaDummy097) := by
  simpa only [nb055AlphaDummy096, nb055AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_102 : (nb055AlphaDummy096) ≠ (nb055AlphaDummy098) := by
  simpa only [nb055AlphaDummy096, nb055AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_103 : (nb055AlphaDummy097) ≠ (nb055AlphaDummy098) := by
  simpa only [nb055AlphaDummy097, nb055AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_104 (x : Var) (y : Var) :
    (nb055AlphaDummy099 x y) ∉
      (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy099] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_105 (x : Var) (y : Var) :
    (nb055AlphaDummy100 x y) ∉
      (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy100] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_106 (x : Var) (y : Var) :
    (nb055AlphaDummy101 x y) ∉
      (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy101] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_107 (x : Var) (y : Var) :
    (nb055AlphaDummy099 x y) ≠ (nb055AlphaDummy100 x y) := by
  simpa only [nb055AlphaDummy099, nb055AlphaDummy100] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_108 (x : Var) (y : Var) :
    (nb055AlphaDummy099 x y) ≠ (nb055AlphaDummy101 x y) := by
  simpa only [nb055AlphaDummy099, nb055AlphaDummy101] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_109 (x : Var) (y : Var) :
    (nb055AlphaDummy100 x y) ≠ (nb055AlphaDummy101 x y) := by
  simpa only [nb055AlphaDummy100, nb055AlphaDummy101] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part003`. -/


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

theorem nb055_fresh_110 :
    (nb055AlphaDummy108) ∉
      (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy097))).fv) :=
  by
  simpa only [nb055AlphaDummy108] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy097))).fv)
      0

theorem nb055_fresh_111 :
    (nb055AlphaDummy104) ∉
      (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv) :=
  by
  simpa only [nb055AlphaDummy104] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv)
      0

theorem nb055_fresh_112 :
    (nb055AlphaDummy110) ∉
      (((Class.cv (nb055AlphaDummy098))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv) :=
  by
  simpa only [nb055AlphaDummy110] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy098))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv)
      0

theorem nb055_fresh_113 (x : Var) (y : Var) :
    (nb055AlphaDummy109 x y) ∉
      (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy100 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy109] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy100 x y))).fv)
      0

theorem nb055_fresh_114 (x : Var) (y : Var) :
    (nb055AlphaDummy105 x y) ∉
      (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy101 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy105] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy101 x y))).fv)
      0

theorem nb055_fresh_115 (x : Var) (y : Var) :
    (nb055AlphaDummy111 x y) ∉
      (((Class.cv (nb055AlphaDummy101 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy101 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy111] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy101 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy101 x y))).fv)
      0

theorem nb055_fresh_116 :
    (nb055AlphaDummy126) ∉ (((Class.cv (nb055AlphaDummy119))).fv) := by
  simpa only [nb055AlphaDummy126] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy119))).fv) 0

theorem nb055_fresh_117 :
    (nb055AlphaDummy127) ∉ (((Class.cv (nb055AlphaDummy119))).fv) := by
  simpa only [nb055AlphaDummy127] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy119))).fv) 1

theorem nb055_distinct_118 : (nb055AlphaDummy126) ≠ (nb055AlphaDummy127) := by
  simpa only [nb055AlphaDummy126, nb055AlphaDummy127] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy119))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_119 (x : Var) (y : Var) :
    (nb055AlphaDummy128 x y) ∉ (((Class.cv (nb055AlphaDummy121 x y))).fv) := by
  simpa only [nb055AlphaDummy128] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy121 x y))).fv) 0

theorem nb055_fresh_120 (x : Var) (y : Var) :
    (nb055AlphaDummy129 x y) ∉ (((Class.cv (nb055AlphaDummy121 x y))).fv) := by
  simpa only [nb055AlphaDummy129] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy121 x y))).fv) 1

theorem nb055_distinct_121 (x : Var) (y : Var) :
    (nb055AlphaDummy128 x y) ≠ (nb055AlphaDummy129 x y) := by
  simpa only [nb055AlphaDummy128, nb055AlphaDummy129] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy121 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_122 :
    (nb055AlphaDummy132) ∉
      (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy132] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_123 :
    (nb055AlphaDummy133) ∉
      (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy133] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_124 :
    (nb055AlphaDummy134) ∉
      (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy134] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_125 : (nb055AlphaDummy132) ≠ (nb055AlphaDummy133) := by
  simpa only [nb055AlphaDummy132, nb055AlphaDummy133] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_126 : (nb055AlphaDummy132) ≠ (nb055AlphaDummy134) := by
  simpa only [nb055AlphaDummy132, nb055AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_127 : (nb055AlphaDummy133) ≠ (nb055AlphaDummy134) := by
  simpa only [nb055AlphaDummy133, nb055AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_128 (x : Var) (y : Var) :
    (nb055AlphaDummy135 x y) ∉
      (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy135] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_129 (x : Var) (y : Var) :
    (nb055AlphaDummy136 x y) ∉
      (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy136] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_130 (x : Var) (y : Var) :
    (nb055AlphaDummy137 x y) ∉
      (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy137] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_131 (x : Var) (y : Var) :
    (nb055AlphaDummy135 x y) ≠ (nb055AlphaDummy136 x y) := by
  simpa only [nb055AlphaDummy135, nb055AlphaDummy136] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_132 (x : Var) (y : Var) :
    (nb055AlphaDummy135 x y) ≠ (nb055AlphaDummy137 x y) := by
  simpa only [nb055AlphaDummy135, nb055AlphaDummy137] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_133 (x : Var) (y : Var) :
    (nb055AlphaDummy136 x y) ≠ (nb055AlphaDummy137 x y) := by
  simpa only [nb055AlphaDummy136, nb055AlphaDummy137] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_134 :
    (nb055AlphaDummy144) ∉
      (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy133))).fv) :=
  by
  simpa only [nb055AlphaDummy144] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy133))).fv)
      0

theorem nb055_fresh_135 :
    (nb055AlphaDummy140) ∉
      (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv) :=
  by
  simpa only [nb055AlphaDummy140] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy133))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv)
      0

theorem nb055_fresh_136 :
    (nb055AlphaDummy146) ∉
      (((Class.cv (nb055AlphaDummy134))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv) :=
  by
  simpa only [nb055AlphaDummy146] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy134))).fv ∪ ((Class.cv (nb055AlphaDummy134))).fv)
      0

theorem nb055_fresh_137 (x : Var) (y : Var) :
    (nb055AlphaDummy145 x y) ∉
      (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy136 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy145] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy136 x y))).fv)
      0

theorem nb055_fresh_138 (x : Var) (y : Var) :
    (nb055AlphaDummy141 x y) ∉
      (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy137 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy141] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy136 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy137 x y))).fv)
      0

theorem nb055_fresh_139 (x : Var) (y : Var) :
    (nb055AlphaDummy147 x y) ∉
      (((Class.cv (nb055AlphaDummy137 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy137 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy147] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy137 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy137 x y))).fv)
      0

theorem nb055_fresh_140 :
    (nb055AlphaDummy162) ∉ (((Class.cv (nb055AlphaDummy155))).fv) := by
  simpa only [nb055AlphaDummy162] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy155))).fv) 0

theorem nb055_fresh_141 :
    (nb055AlphaDummy163) ∉ (((Class.cv (nb055AlphaDummy155))).fv) := by
  simpa only [nb055AlphaDummy163] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy155))).fv) 1

theorem nb055_distinct_142 : (nb055AlphaDummy162) ≠ (nb055AlphaDummy163) := by
  simpa only [nb055AlphaDummy162, nb055AlphaDummy163] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy155))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_143 (x : Var) (y : Var) :
    (nb055AlphaDummy164 x y) ∉ (((Class.cv (nb055AlphaDummy157 x y))).fv) := by
  simpa only [nb055AlphaDummy164] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy157 x y))).fv) 0

theorem nb055_fresh_144 (x : Var) (y : Var) :
    (nb055AlphaDummy165 x y) ∉ (((Class.cv (nb055AlphaDummy157 x y))).fv) := by
  simpa only [nb055AlphaDummy165] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy157 x y))).fv) 1

theorem nb055_distinct_145 (x : Var) (y : Var) :
    (nb055AlphaDummy164 x y) ≠ (nb055AlphaDummy165 x y) := by
  simpa only [nb055AlphaDummy164, nb055AlphaDummy165] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy157 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb055_fresh_146 :
    (nb055AlphaDummy168) ∉
      (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy168] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_147 :
    (nb055AlphaDummy169) ∉
      (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy169] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_148 :
    (nb055AlphaDummy170) ∉
      (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy170] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_149 : (nb055AlphaDummy168) ≠ (nb055AlphaDummy169) := by
  simpa only [nb055AlphaDummy168, nb055AlphaDummy169] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb055_distinct_150 : (nb055AlphaDummy168) ≠ (nb055AlphaDummy170) := by
  simpa only [nb055AlphaDummy168, nb055AlphaDummy170] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb055_distinct_151 : (nb055AlphaDummy169) ≠ (nb055AlphaDummy170) := by
  simpa only [nb055AlphaDummy169, nb055AlphaDummy170] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb055_fresh_152 (x : Var) (y : Var) :
    (nb055AlphaDummy171 x y) ∉
      (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy171] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb055_fresh_153 (x : Var) (y : Var) :
    (nb055AlphaDummy172 x y) ∉
      (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy172] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb055_fresh_154 (x : Var) (y : Var) :
    (nb055AlphaDummy173 x y) ∉
      (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb055AlphaDummy173] using
    freshVar_not_mem (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb055_distinct_155 (x : Var) (y : Var) :
    (nb055AlphaDummy171 x y) ≠ (nb055AlphaDummy172 x y) := by
  simpa only [nb055AlphaDummy171, nb055AlphaDummy172] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_distinct_156 (x : Var) (y : Var) :
    (nb055AlphaDummy171 x y) ≠ (nb055AlphaDummy173 x y) := by
  simpa only [nb055AlphaDummy171, nb055AlphaDummy173] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb055_distinct_157 (x : Var) (y : Var) :
    (nb055AlphaDummy172 x y) ≠ (nb055AlphaDummy173 x y) := by
  simpa only [nb055AlphaDummy172, nb055AlphaDummy173] using
    (freshVar_injective (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb055_fresh_158 :
    (nb055AlphaDummy180) ∉
      (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy169))).fv) :=
  by
  simpa only [nb055AlphaDummy180] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy169))).fv)
      0

theorem nb055_fresh_159 :
    (nb055AlphaDummy176) ∉
      (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv) :=
  by
  simpa only [nb055AlphaDummy176] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy169))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv)
      0

theorem nb055_fresh_160 :
    (nb055AlphaDummy182) ∉
      (((Class.cv (nb055AlphaDummy170))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv) :=
  by
  simpa only [nb055AlphaDummy182] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy170))).fv ∪ ((Class.cv (nb055AlphaDummy170))).fv)
      0

theorem nb055_fresh_161 (x : Var) (y : Var) :
    (nb055AlphaDummy181 x y) ∉
      (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy172 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy181] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy172 x y))).fv)
      0

theorem nb055_fresh_162 (x : Var) (y : Var) :
    (nb055AlphaDummy177 x y) ∉
      (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy173 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy177] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy172 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy173 x y))).fv)
      0

theorem nb055_fresh_163 (x : Var) (y : Var) :
    (nb055AlphaDummy183 x y) ∉
      (((Class.cv (nb055AlphaDummy173 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy173 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy183] using
    freshVar_not_mem
      (((Class.cv (nb055AlphaDummy173 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy173 x y))).fv)
      0

theorem nb055_fresh_164 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055AlphaDummy016] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb055_fresh_165 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055AlphaDummy017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb055_fresh_166 (x : Var) (y : Var) :
    (nb055AlphaDummy079 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055AlphaDummy079] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2

theorem nb055_distinct_167 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ≠ (nb055AlphaDummy017 x y) := by
  simpa only [nb055AlphaDummy016, nb055AlphaDummy017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_168 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ≠ (nb055AlphaDummy079 x y) := by
  simpa only [nb055AlphaDummy016, nb055AlphaDummy079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_169 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ≠ (nb055AlphaDummy079 x y) := by
  simpa only [nb055AlphaDummy017, nb055AlphaDummy079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_170 :
    (nb055AlphaDummy026) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy022))).fv) :=
  by
  simpa only [nb055AlphaDummy026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy022))).fv)
      0

theorem nb055_fresh_171 (x : Var) (y : Var) :
    (nb055AlphaDummy027 x y) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy024 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy024 x y))).fv)
      0

theorem nb055_fresh_172 :
    (nb055AlphaDummy054) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy050))).fv) :=
  by
  simpa only [nb055AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy050))).fv)
      0

theorem nb055_fresh_173 (x : Var) (y : Var) :
    (nb055AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy052 x y))).fv)
      0

theorem nb055_fresh_174 :
    (nb055AlphaDummy094) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy090)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy090)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy090))).fv) :=
  by
  simpa only [nb055AlphaDummy094] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy090)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy090)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy090))).fv)
      0

theorem nb055_fresh_175 (x : Var) (y : Var) :
    (nb055AlphaDummy095 x y) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy092 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy092 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy092 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy095] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy092 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy092 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy092 x y))).fv)
      0

theorem nb055_fresh_176 :
    (nb055AlphaDummy130) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy126)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy126)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy126))).fv) :=
  by
  simpa only [nb055AlphaDummy130] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy126)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy126)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy126))).fv)
      0

theorem nb055_fresh_177 (x : Var) (y : Var) :
    (nb055AlphaDummy131 x y) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy128 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy128 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy128 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy131] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy128 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy128 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy128 x y))).fv)
      0

theorem nb055_fresh_178 :
    (nb055AlphaDummy166) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy162)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy162)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy162))).fv) :=
  by
  simpa only [nb055AlphaDummy166] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy162)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy162)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy162))).fv)
      0

theorem nb055_fresh_179 (x : Var) (y : Var) :
    (nb055AlphaDummy167 x y) ∉
      (((Wff.classMem (Class.cv (nb055AlphaDummy164 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy164 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy164 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy167] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb055AlphaDummy164 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy164 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy164 x y))).fv)
      0

theorem nb055_fresh_180 :
    (nb055AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
                (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCphi (Class.cv (nb055AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy006)
              (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
                (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCphi (Class.cv (nb055AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy006)
              (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_181 (x : Var) (y : Var) :
    (nb055AlphaDummy011 x y) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_182 :
    (nb055AlphaDummy018) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCphi (Class.cv (nb055AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy018] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCphi (Class.cv (nb055AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_183 (x : Var) (y : Var) :
    (nb055AlphaDummy019 x y) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCphi (Class.cv (nb055AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy019] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCphi (Class.cv (nb055AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_184 :
    (nb055AlphaDummy086) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCphi (Class.cv (nb055AlphaDummy083)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy086] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCphi (Class.cv (nb055AlphaDummy083)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_185 (x : Var) (y : Var) :
    (nb055AlphaDummy087 x y) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCphi (Class.cv (nb055AlphaDummy085 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy087] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCphi (Class.cv (nb055AlphaDummy085 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_186 :
    (nb055AlphaDummy122) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCphi (Class.cv (nb055AlphaDummy119)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy122] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCphi (Class.cv (nb055AlphaDummy119)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_187 (x : Var) (y : Var) :
    (nb055AlphaDummy123 x y) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCphi (Class.cv (nb055AlphaDummy121 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy123] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCphi (Class.cv (nb055AlphaDummy121 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_188 :
    (nb055AlphaDummy158) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCphi (Class.cv (nb055AlphaDummy155)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy158] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCphi (Class.cv (nb055AlphaDummy155)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_189 (x : Var) (y : Var) :
    (nb055AlphaDummy159 x y) ∉
      (((synCcompl (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCphi (Class.cv (nb055AlphaDummy157 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb055AlphaDummy159] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCphi (Class.cv (nb055AlphaDummy157 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb055_fresh_190 :
    (nb055AlphaDummy038) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy030)))).fv) :=
  by
  simpa only [nb055AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy030)))).fv)
      0

theorem nb055_fresh_191 (x : Var) (y : Var) :
    (nb055AlphaDummy039 x y) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy033 x y)))).fv)
      0

theorem nb055_fresh_192 :
    (nb055AlphaDummy066) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy058)))).fv) :=
  by
  simpa only [nb055AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy058)))).fv)
      0

theorem nb055_fresh_193 (x : Var) (y : Var) :
    (nb055AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy061 x y)))).fv)
      0

theorem nb055_fresh_194 :
    (nb055AlphaDummy106) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy097)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy098)))).fv) :=
  by
  simpa only [nb055AlphaDummy106] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy097)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy098)))).fv)
      0

theorem nb055_fresh_195 (x : Var) (y : Var) :
    (nb055AlphaDummy107 x y) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy100 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy101 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy107] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy100 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy101 x y)))).fv)
      0

theorem nb055_fresh_196 :
    (nb055AlphaDummy142) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy133)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy134)))).fv) :=
  by
  simpa only [nb055AlphaDummy142] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy133)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy134)))).fv)
      0

theorem nb055_fresh_197 (x : Var) (y : Var) :
    (nb055AlphaDummy143 x y) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy136 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy137 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy143] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy136 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy137 x y)))).fv)
      0

theorem nb055_fresh_198 :
    (nb055AlphaDummy178) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy169)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy170)))).fv) :=
  by
  simpa only [nb055AlphaDummy178] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy169)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy170)))).fv)
      0

theorem nb055_fresh_199 (x : Var) (y : Var) :
    (nb055AlphaDummy179 x y) ∉
      (((synCcompl (Class.cv (nb055AlphaDummy172 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy173 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy179] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb055AlphaDummy172 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy173 x y)))).fv)
      0

theorem nb055_fresh_200 :
    (nb055AlphaDummy074) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_201 (x : Var) (y : Var) :
    (nb055AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_202 :
    (nb055AlphaDummy046) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_203 (x : Var) (y : Var) :
    (nb055AlphaDummy047 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_204 :
    (nb055AlphaDummy114) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy083))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy114] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy083))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_205 (x : Var) (y : Var) :
    (nb055AlphaDummy115 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy085 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy115] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy085 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_206 :
    (nb055AlphaDummy150) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy119))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy150] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy119))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_207 (x : Var) (y : Var) :
    (nb055AlphaDummy151 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy121 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy151] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy121 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_208 :
    (nb055AlphaDummy186) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy155))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy186] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy155))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_209 (x : Var) (y : Var) :
    (nb055AlphaDummy187 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy157 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb055AlphaDummy187] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy157 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb055_fresh_210 :
    (nb055AlphaDummy034) ∉
      (((synCnin (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy029))
            (Class.cv (nb055AlphaDummy030)))).fv) :=
  by
  simpa only [nb055AlphaDummy034] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030)))).fv)
      0

theorem nb055_fresh_211 (x : Var) (y : Var) :
    (nb055AlphaDummy035 x y) ∉
      (((synCnin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy035] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y)))).fv)
      0

theorem nb055_fresh_212 :
    (nb055AlphaDummy062) ∉
      (((synCnin (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy057))
            (Class.cv (nb055AlphaDummy058)))).fv) :=
  by
  simpa only [nb055AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058)))).fv)
      0

theorem nb055_fresh_213 (x : Var) (y : Var) :
    (nb055AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y)))).fv)
      0

theorem nb055_fresh_214 :
    (nb055AlphaDummy102) ∉
      (((synCnin (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy097))
            (Class.cv (nb055AlphaDummy098)))).fv) :=
  by
  simpa only [nb055AlphaDummy102] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098)))).fv)
      0

theorem nb055_fresh_215 (x : Var) (y : Var) :
    (nb055AlphaDummy103 x y) ∉
      (((synCnin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy103] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y)))).fv)
      0

theorem nb055_fresh_216 :
    (nb055AlphaDummy138) ∉
      (((synCnin (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy133))
            (Class.cv (nb055AlphaDummy134)))).fv) :=
  by
  simpa only [nb055AlphaDummy138] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134)))).fv)
      0

theorem nb055_fresh_217 (x : Var) (y : Var) :
    (nb055AlphaDummy139 x y) ∉
      (((synCnin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy139] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y)))).fv)
      0

theorem nb055_fresh_218 :
    (nb055AlphaDummy174) ∉
      (((synCnin (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy169))
            (Class.cv (nb055AlphaDummy170)))).fv) :=
  by
  simpa only [nb055AlphaDummy174] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170)))).fv)
      0

theorem nb055_fresh_219 (x : Var) (y : Var) :
    (nb055AlphaDummy175 x y) ∉
      (((synCnin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy175] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y)))).fv)
      0

theorem nb055_fresh_220 :
    (nb055AlphaDummy006) ∉
      (((synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv ∪
        ((Class.cv (nb055AlphaDummy002))).fv) :=
  by
  simpa only [nb055AlphaDummy006] using
    freshVar_not_mem
      (((synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv ∪
        ((Class.cv (nb055AlphaDummy002))).fv)
      0

theorem nb055_fresh_221 :
    (nb055AlphaDummy007) ∉
      (((synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv ∪
        ((Class.cv (nb055AlphaDummy002))).fv) :=
  by
  simpa only [nb055AlphaDummy007] using
    freshVar_not_mem
      (((synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv ∪
        ((Class.cv (nb055AlphaDummy002))).fv)
      1

theorem nb055_distinct_222 : (nb055AlphaDummy006) ≠ (nb055AlphaDummy007) := by
  simpa only [nb055AlphaDummy006, nb055AlphaDummy007] using
    (freshVar_injective (((synCop (Class.cv (nb055AlphaDummy000))
            (Class.cv (nb055AlphaDummy001)))).fv ∪ ((Class.cv (nb055AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb055_fresh_223 (x : Var) (y : Var) :
    (nb055AlphaDummy008 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy008] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055AlphaDummy003 x y))).fv)
      0

theorem nb055_fresh_224 (x : Var) (y : Var) :
    (nb055AlphaDummy009 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb055AlphaDummy009] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055AlphaDummy003 x y))).fv)
      1

theorem nb055_distinct_225 (x : Var) (y : Var) :
    (nb055AlphaDummy008 x y) ≠ (nb055AlphaDummy009 x y) := by
  simpa only [nb055AlphaDummy008, nb055AlphaDummy009] using
    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055AlphaDummy003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_226 :
    (nb055AlphaDummy076) ∉
      (((synCphi (Class.cv (nb055AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy007)))).fv) :=
  by
  simpa only [nb055AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy007)))).fv)
      0

theorem nb055_fresh_227 (x : Var) (y : Var) :
    (nb055AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb055AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy009 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy009 x y)))).fv)
      0

theorem nb055_fresh_228 :
    (nb055AlphaDummy048) ∉
      (((synCphi (Class.cv (nb055AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy015)))).fv) :=
  by
  simpa only [nb055AlphaDummy048] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy015)))).fv)
      0

theorem nb055_fresh_229 (x : Var) (y : Var) :
    (nb055AlphaDummy049 x y) ∉
      (((synCphi (Class.cv (nb055AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy017 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy049] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy017 x y)))).fv)
      0

theorem nb055_fresh_230 :
    (nb055AlphaDummy116) ∉
      (((synCphi (Class.cv (nb055AlphaDummy083)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy083)))).fv) :=
  by
  simpa only [nb055AlphaDummy116] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy083)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy083)))).fv)
      0

theorem nb055_fresh_231 (x : Var) (y : Var) :
    (nb055AlphaDummy117 x y) ∉
      (((synCphi (Class.cv (nb055AlphaDummy085 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy085 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy117] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy085 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy085 x y)))).fv)
      0

theorem nb055_fresh_232 :
    (nb055AlphaDummy152) ∉
      (((synCphi (Class.cv (nb055AlphaDummy119)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy119)))).fv) :=
  by
  simpa only [nb055AlphaDummy152] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy119)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy119)))).fv)
      0

theorem nb055_fresh_233 (x : Var) (y : Var) :
    (nb055AlphaDummy153 x y) ∉
      (((synCphi (Class.cv (nb055AlphaDummy121 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy121 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy153] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy121 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy121 x y)))).fv)
      0

theorem nb055_fresh_234 :
    (nb055AlphaDummy188) ∉
      (((synCphi (Class.cv (nb055AlphaDummy155)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy155)))).fv) :=
  by
  simpa only [nb055AlphaDummy188] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy155)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy155)))).fv)
      0

theorem nb055_fresh_235 (x : Var) (y : Var) :
    (nb055AlphaDummy189 x y) ∉
      (((synCphi (Class.cv (nb055AlphaDummy157 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy157 x y)))).fv) :=
  by
  simpa only [nb055AlphaDummy189] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb055AlphaDummy157 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy157 x y)))).fv)
      0

theorem nb055_fresh_236 :
    (nb055AlphaDummy002) ∉
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb055AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCcom (Class.cv (nb055AlphaDummy000))
            (Class.cv (nb055AlphaDummy001)))).fv) :=
  by
  simpa only [nb055AlphaDummy002] using
    freshVar_not_mem
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb055AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCcom (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv)
      0

theorem nb055_fresh_237 :
    (nb055AlphaDummy004) ∉
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
          ({(nb055AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))).fv) :=
  by
  simpa only [nb055AlphaDummy004] using
    freshVar_not_mem
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
          ({(nb055AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))).fv)
      0

theorem nb055_fresh_238 :
    (nb055AlphaDummy080) ∉
      (({(nb055AlphaDummy014)} : Finset Var) ∪ ({(nb055AlphaDummy015)} : Finset Var) ∪
        ((synWex (nb055AlphaDummy078) (synWa (synWbr (Class.cv (nb055AlphaDummy014))
                (Class.cv (nb055AlphaDummy001)) (Class.cv (nb055AlphaDummy078)))
              (synWbr (Class.cv (nb055AlphaDummy078)) (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy015)))))).fv) :=
  by
  simpa only [nb055AlphaDummy080] using
    freshVar_not_mem
      (({(nb055AlphaDummy014)} : Finset Var) ∪ ({(nb055AlphaDummy015)} : Finset Var) ∪
        ((synWex (nb055AlphaDummy078) (synWa (synWbr (Class.cv (nb055AlphaDummy014))
                (Class.cv (nb055AlphaDummy001)) (Class.cv (nb055AlphaDummy078)))
              (synWbr (Class.cv (nb055AlphaDummy078)) (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy015)))))).fv)
      0

theorem nb055_fresh_239 (x : Var) (y : Var) :
    (nb055AlphaDummy081 x y) ∉
      (({(nb055AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb055AlphaDummy017 x y)} : Finset Var) ∪ ((synWex (nb055AlphaDummy079 x y)
            (synWa (synWbr (Class.cv (nb055AlphaDummy016 x y)) (Class.cv y)
                (Class.cv (nb055AlphaDummy079 x y)))
              (synWbr (Class.cv (nb055AlphaDummy079 x y)) (Class.cv x)
                (Class.cv (nb055AlphaDummy017 x y)))))).fv) :=
  by
  simpa only [nb055AlphaDummy081] using
    freshVar_not_mem
      (({(nb055AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb055AlphaDummy017 x y)} : Finset Var) ∪ ((synWex (nb055AlphaDummy079 x y)
            (synWa (synWbr (Class.cv (nb055AlphaDummy016 x y)) (Class.cv y)
                (Class.cv (nb055AlphaDummy079 x y)))
              (synWbr (Class.cv (nb055AlphaDummy079 x y)) (Class.cv x)
                (Class.cv (nb055AlphaDummy017 x y)))))).fv)
      0

theorem nb055_fresh_240 (x : Var) (y : Var) :
    (nb055AlphaDummy003 x y) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCcom (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb055AlphaDummy003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCcom (Class.cv x) (Class.cv y))).fv)
      0

theorem nb055_fresh_241 (x : Var) (y : Var) :
    (nb055AlphaDummy005 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb055AlphaDummy005] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb055_fresh_242 : (nb055AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb055AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb055_fresh_243 : (nb055AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb055AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb055_distinct_244 : (nb055AlphaDummy000) ≠ (nb055AlphaDummy001) := by
  simpa only [nb055AlphaDummy000, nb055AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb055_support_mem_0000 :
    (nb055AlphaDummy000) ∈
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
          ({(nb055AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb055AlphaDummy000)) (s :=
        ({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
          ({(nb055AlphaDummy002)} : Finset Var))
        ((synWa (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055AlphaDummy003 x y)} : Finset Var))
        ((synWa (synWa (Wff.classMem (Class.cv x) (synCvv))
              (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0002 :
    (nb055AlphaDummy001) ∈
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
          ({(nb055AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb055AlphaDummy001)) (s :=
        ({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
          ({(nb055AlphaDummy002)} : Finset Var))
        ((synWa (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055AlphaDummy003 x y)} : Finset Var))
        ((synWa (synWa (Wff.classMem (Class.cv x) (synCvv))
              (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0004 :
    (nb055AlphaDummy002) ∈
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
          ({(nb055AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb055AlphaDummy002)) (s :=
        ({(nb055AlphaDummy000)} : Finset Var) ∪ ({(nb055AlphaDummy001)} : Finset Var) ∪
          ({(nb055AlphaDummy002)} : Finset Var))
        ((synWa (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0005 (x : Var) (y : Var) :
    (nb055AlphaDummy003 x y) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb055AlphaDummy003 x y)) (s :=
        ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb055AlphaDummy003 x y)} : Finset Var))
        ((synWa (synWa (Wff.classMem (Class.cv x) (synCvv))
              (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0006 :
    (nb055AlphaDummy000) ∈
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb055AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCcom (Class.cv (nb055AlphaDummy000))
            (Class.cv (nb055AlphaDummy001)))).fv) :=
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

theorem nb055_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCcom (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s :=
        ({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv)
        ((synCcom (Class.cv x) (Class.cv y))).fv ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0008 :
    (nb055AlphaDummy000) ∈
      (((synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv ∪
        ((Class.cv (nb055AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part004`. -/


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

theorem nb055_support_mem_0009 :
    (nb055AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
                (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCphi (Class.cv (nb055AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy006)
              (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0010 (x : Var) (y : Var) :
    x ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0011 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := x) (s := ((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv)
        ((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0012 :
    (nb055AlphaDummy000) ∈
      (((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007))))))).fv ∪
        ((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0014 :
    (nb055AlphaDummy000) ∈
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0015 :
    (nb055AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCphi (Class.cv (nb055AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCphi (Class.cv (nb055AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0018 :
    (nb055AlphaDummy000) ∈
      (((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCphi (Class.cv (nb055AlphaDummy015))))))).fv ∪
        ((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCphi (Class.cv (nb055AlphaDummy015))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCphi (Class.cv (nb055AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCphi (Class.cv (nb055AlphaDummy017 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0020 :
    (nb055AlphaDummy015) ∈ (((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0021 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈ (((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0022 :
    (nb055AlphaDummy022) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy022))).fv) :=
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

theorem nb055_support_mem_0023 (x : Var) (y : Var) :
    (nb055AlphaDummy024 x y) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy024 x y))).fv) :=
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

theorem nb055_support_mem_0024 :
    (nb055AlphaDummy022) ∈
      (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0025 (x : Var) (y : Var) :
    (nb055AlphaDummy024 x y) ∈
      (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0026 :
    (nb055AlphaDummy029) ∈
      (((synCnin (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy029))
            (Class.cv (nb055AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0027 (x : Var) (y : Var) :
    (nb055AlphaDummy032 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0028 :
    (nb055AlphaDummy029) ∈
      (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0029 (x : Var) (y : Var) :
    (nb055AlphaDummy032 x y) ∈
      (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0030 :
    (nb055AlphaDummy030) ∈
      (((synCnin (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy029))
            (Class.cv (nb055AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0031 (x : Var) (y : Var) :
    (nb055AlphaDummy033 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0032 :
    (nb055AlphaDummy030) ∈
      (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0033 (x : Var) (y : Var) :
    (nb055AlphaDummy033 x y) ∈
      (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0034 :
    (nb055AlphaDummy029) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0035 (x : Var) (y : Var) :
    (nb055AlphaDummy032 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0036 :
    (nb055AlphaDummy029) ∈
      (((Class.cv (nb055AlphaDummy029))).fv ∪ ((Class.cv (nb055AlphaDummy029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0037 (x : Var) (y : Var) :
    (nb055AlphaDummy032 x y) ∈
      (((Class.cv (nb055AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy032 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0038 :
    (nb055AlphaDummy030) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0039 (x : Var) (y : Var) :
    (nb055AlphaDummy033 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0040 :
    (nb055AlphaDummy030) ∈
      (((Class.cv (nb055AlphaDummy030))).fv ∪ ((Class.cv (nb055AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0041 (x : Var) (y : Var) :
    (nb055AlphaDummy033 x y) ∈
      (((Class.cv (nb055AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0042 :
    (nb055AlphaDummy001) ∈
      (({(nb055AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb055AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCcom (Class.cv (nb055AlphaDummy000))
            (Class.cv (nb055AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0043 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCcom (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s :=
        ({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv)
        ((synCcom (Class.cv x) (Class.cv y))).fv ?_
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0044 :
    (nb055AlphaDummy001) ∈
      (((synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv ∪
        ((Class.cv (nb055AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0045 :
    (nb055AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
                (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCphi (Class.cv (nb055AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy006)
              (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0046 (x : Var) (y : Var) :
    y ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := y) (s := ((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv)
        ((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0048 :
    (nb055AlphaDummy001) ∈
      (((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007))))))).fv ∪
        ((Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
              (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCphi (Class.cv (nb055AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0049 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCphi (Class.cv (nb055AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0050 :
    (nb055AlphaDummy001) ∈
      (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0051 :
    (nb055AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy000))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCphi (Class.cv (nb055AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCphi (Class.cv (nb055AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0054 :
    (nb055AlphaDummy001) ∈
      (((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0056 :
    (nb055AlphaDummy015) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0057 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0058 :
    (nb055AlphaDummy015) ∈
      (((synCphi (Class.cv (nb055AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy015)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0059 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (((synCphi (Class.cv (nb055AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy017 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0060 :
    (nb055AlphaDummy007) ∈ (((Class.cv (nb055AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0061 (x : Var) (y : Var) :
    (nb055AlphaDummy009 x y) ∈ (((Class.cv (nb055AlphaDummy009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0062 :
    (nb055AlphaDummy050) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy050))).fv) :=
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

theorem nb055_support_mem_0063 (x : Var) (y : Var) :
    (nb055AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy052 x y))).fv) :=
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

theorem nb055_support_mem_0064 :
    (nb055AlphaDummy050) ∈
      (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0065 (x : Var) (y : Var) :
    (nb055AlphaDummy052 x y) ∈
      (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0066 :
    (nb055AlphaDummy057) ∈
      (((synCnin (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy057))
            (Class.cv (nb055AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0067 (x : Var) (y : Var) :
    (nb055AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0068 :
    (nb055AlphaDummy057) ∈
      (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0069 (x : Var) (y : Var) :
    (nb055AlphaDummy060 x y) ∈
      (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0070 :
    (nb055AlphaDummy058) ∈
      (((synCnin (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy057))
            (Class.cv (nb055AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0071 (x : Var) (y : Var) :
    (nb055AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0072 :
    (nb055AlphaDummy058) ∈
      (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0073 (x : Var) (y : Var) :
    (nb055AlphaDummy061 x y) ∈
      (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0074 :
    (nb055AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0075 (x : Var) (y : Var) :
    (nb055AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0076 :
    (nb055AlphaDummy057) ∈
      (((Class.cv (nb055AlphaDummy057))).fv ∪ ((Class.cv (nb055AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0077 (x : Var) (y : Var) :
    (nb055AlphaDummy060 x y) ∈
      (((Class.cv (nb055AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0078 :
    (nb055AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0079 (x : Var) (y : Var) :
    (nb055AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0080 :
    (nb055AlphaDummy058) ∈
      (((Class.cv (nb055AlphaDummy058))).fv ∪ ((Class.cv (nb055AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0081 (x : Var) (y : Var) :
    (nb055AlphaDummy061 x y) ∈
      (((Class.cv (nb055AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0082 :
    (nb055AlphaDummy002) ∈
      (((synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))).fv ∪
        ((Class.cv (nb055AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0083 :
    (nb055AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
                (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCphi (Class.cv (nb055AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy006)
              (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0084 (x : Var) (y : Var) :
    (nb055AlphaDummy003 x y) ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb055AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0085 (x : Var) (y : Var) :
    (nb055AlphaDummy003 x y) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := (nb055AlphaDummy003 x y)) (t := ((synCcompl
            (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv)
        ((synCcompl (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0086 :
    (nb055AlphaDummy002) ∈
      (((Class.cab (nb055AlphaDummy006)
            (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy006)
            (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
              (Wff.classEq (Class.cv (nb055AlphaDummy006))
                (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0087 (x : Var) (y : Var) :
    (nb055AlphaDummy003 x y) ∈
      (((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy008 x y)
            (synWrex (nb055AlphaDummy009 x y) (Class.cv (nb055AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0088 :
    (nb055AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0089 (x : Var) (y : Var) :
    (nb055AlphaDummy009 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0090 :
    (nb055AlphaDummy007) ∈
      (((synCphi (Class.cv (nb055AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0091 (x : Var) (y : Var) :
    (nb055AlphaDummy009 x y) ∈
      (((synCphi (Class.cv (nb055AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0092 :
    (nb055AlphaDummy014) ∈
      (({(nb055AlphaDummy014)} : Finset Var) ∪ ({(nb055AlphaDummy015)} : Finset Var) ∪
        ((synWex (nb055AlphaDummy078) (synWa (synWbr (Class.cv (nb055AlphaDummy014))
                (Class.cv (nb055AlphaDummy001)) (Class.cv (nb055AlphaDummy078)))
              (synWbr (Class.cv (nb055AlphaDummy078)) (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy015)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0093 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ∈
      (({(nb055AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb055AlphaDummy017 x y)} : Finset Var) ∪ ((synWex (nb055AlphaDummy079 x y)
            (synWa (synWbr (Class.cv (nb055AlphaDummy016 x y)) (Class.cv y)
                (Class.cv (nb055AlphaDummy079 x y)))
              (synWbr (Class.cv (nb055AlphaDummy079 x y)) (Class.cv x)
                (Class.cv (nb055AlphaDummy017 x y)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0094 :
    (nb055AlphaDummy015) ∈
      (({(nb055AlphaDummy014)} : Finset Var) ∪ ({(nb055AlphaDummy015)} : Finset Var) ∪
        ((synWex (nb055AlphaDummy078) (synWa (synWbr (Class.cv (nb055AlphaDummy014))
                (Class.cv (nb055AlphaDummy001)) (Class.cv (nb055AlphaDummy078)))
              (synWbr (Class.cv (nb055AlphaDummy078)) (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy015)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0095 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (({(nb055AlphaDummy016 x y)} : Finset Var) ∪
          ({(nb055AlphaDummy017 x y)} : Finset Var) ∪ ((synWex (nb055AlphaDummy079 x y)
            (synWa (synWbr (Class.cv (nb055AlphaDummy016 x y)) (Class.cv y)
                (Class.cv (nb055AlphaDummy079 x y)))
              (synWbr (Class.cv (nb055AlphaDummy079 x y)) (Class.cv x)
                (Class.cv (nb055AlphaDummy017 x y)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0096 :
    (nb055AlphaDummy014) ∈
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0097 :
    (nb055AlphaDummy014) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCphi (Class.cv (nb055AlphaDummy083)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0098 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ∈
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0099 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCphi (Class.cv (nb055AlphaDummy085 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0100 :
    (nb055AlphaDummy014) ∈
      (((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCphi (Class.cv (nb055AlphaDummy083))))))).fv ∪
        ((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCphi (Class.cv (nb055AlphaDummy083))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0101 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ∈
      (((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCphi (Class.cv (nb055AlphaDummy085 x y))))))).fv ∪
        ((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCphi (Class.cv (nb055AlphaDummy085 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0102 :
    (nb055AlphaDummy083) ∈ (((Class.cv (nb055AlphaDummy083))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0103 (x : Var) (y : Var) :
    (nb055AlphaDummy085 x y) ∈ (((Class.cv (nb055AlphaDummy085 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0104 :
    (nb055AlphaDummy090) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy090)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy090)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy090))).fv) :=
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

theorem nb055_support_mem_0105 (x : Var) (y : Var) :
    (nb055AlphaDummy092 x y) ∈
      (((Wff.classMem (Class.cv (nb055AlphaDummy092 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb055AlphaDummy092 x y)) (synC1c))).fv ∪
        ((Class.cv (nb055AlphaDummy092 x y))).fv) :=
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

theorem nb055_support_mem_0106 :
    (nb055AlphaDummy090) ∈
      (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0107 (x : Var) (y : Var) :
    (nb055AlphaDummy092 x y) ∈
      (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0108 :
    (nb055AlphaDummy097) ∈
      (((synCnin (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy097))
            (Class.cv (nb055AlphaDummy098)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0109 (x : Var) (y : Var) :
    (nb055AlphaDummy100 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0110 :
    (nb055AlphaDummy097) ∈
      (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0111 (x : Var) (y : Var) :
    (nb055AlphaDummy100 x y) ∈
      (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy101 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0112 :
    (nb055AlphaDummy098) ∈
      (((synCnin (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy097))
            (Class.cv (nb055AlphaDummy098)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0113 (x : Var) (y : Var) :
    (nb055AlphaDummy101 x y) ∈
      (((synCnin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y)))).fv ∪
        ((synCnin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0114 :
    (nb055AlphaDummy098) ∈
      (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0115 (x : Var) (y : Var) :
    (nb055AlphaDummy101 x y) ∈
      (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy101 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0116 :
    (nb055AlphaDummy097) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy097)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy098)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0117 (x : Var) (y : Var) :
    (nb055AlphaDummy100 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy100 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy101 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0118 :
    (nb055AlphaDummy097) ∈
      (((Class.cv (nb055AlphaDummy097))).fv ∪ ((Class.cv (nb055AlphaDummy097))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0119 (x : Var) (y : Var) :
    (nb055AlphaDummy100 x y) ∈
      (((Class.cv (nb055AlphaDummy100 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy100 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0120 :
    (nb055AlphaDummy098) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy097)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy098)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0121 (x : Var) (y : Var) :
    (nb055AlphaDummy101 x y) ∈
      (((synCcompl (Class.cv (nb055AlphaDummy100 x y)))).fv ∪
        ((synCcompl (Class.cv (nb055AlphaDummy101 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0122 :
    (nb055AlphaDummy098) ∈
      (((Class.cv (nb055AlphaDummy098))).fv ∪ ((Class.cv (nb055AlphaDummy098))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0123 (x : Var) (y : Var) :
    (nb055AlphaDummy101 x y) ∈
      (((Class.cv (nb055AlphaDummy101 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy101 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0124 :
    (nb055AlphaDummy015) ∈
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0125 :
    (nb055AlphaDummy015) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy014))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCphi (Class.cv (nb055AlphaDummy083)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0126 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0127 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCphi (Class.cv (nb055AlphaDummy085 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0128 :
    (nb055AlphaDummy015) ∈
      (((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0129 (x : Var) (y : Var) :
    (nb055AlphaDummy017 x y) ∈
      (((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0130 :
    (nb055AlphaDummy083) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy083))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0131 (x : Var) (y : Var) :
    (nb055AlphaDummy085 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb055AlphaDummy085 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0132 :
    (nb055AlphaDummy083) ∈
      (((synCphi (Class.cv (nb055AlphaDummy083)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy083)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0133 (x : Var) (y : Var) :
    (nb055AlphaDummy085 x y) ∈
      (((synCphi (Class.cv (nb055AlphaDummy085 x y)))).fv ∪
        ((synCphi (Class.cv (nb055AlphaDummy085 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0134 :
    (nb055AlphaDummy014) ∈
      (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0135 :
    (nb055AlphaDummy014) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy014))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCphi (Class.cv (nb055AlphaDummy119)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0136 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ∈
      (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
        ((Class.cv (nb055AlphaDummy079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0137 (x : Var) (y : Var) :
    (nb055AlphaDummy016 x y) ∈
      (((synCcompl (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCphi (Class.cv (nb055AlphaDummy121 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
