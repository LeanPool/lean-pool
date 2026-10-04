/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4H5C094M3Part001. -/


public section


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

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_000`. -/
@[expose]
noncomputable def nb094AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_001`. -/
@[expose]
noncomputable def nb094AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_002`. -/
@[expose]
noncomputable def nb094AlphaDummy002 : Var :=
  (freshVar (({(nb094AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
          ({(nb094AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCdif (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_003`. -/
@[expose]
noncomputable def nb094AlphaDummy003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
      ((synCdif (Class.cv x) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_004`. -/
@[expose]
noncomputable def nb094AlphaDummy004 : Var :=
  (freshVar
    (({(nb094AlphaDummy000)} : Finset Var) ∪ ({(nb094AlphaDummy001)} : Finset Var) ∪
        ({(nb094AlphaDummy002)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv (nb094AlphaDummy000)) (synCvv))
            (Wff.classMem (Class.cv (nb094AlphaDummy001)) (synCvv)))
          (Wff.classEq (Class.cv (nb094AlphaDummy002))
            (synCdif (Class.cv (nb094AlphaDummy000))
              (Class.cv (nb094AlphaDummy001)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_005`. -/
@[expose]
noncomputable def nb094AlphaDummy005 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb094AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
          (Wff.classEq (Class.cv (nb094AlphaDummy003 x y))
            (synCdif (Class.cv x) (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_006`. -/
@[expose]
noncomputable def nb094AlphaDummy006 : Var :=
  (freshVar (((synCop (Class.cv (nb094AlphaDummy000))
          (Class.cv (nb094AlphaDummy001)))).fv ∪ ((Class.cv (nb094AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_007`. -/
@[expose]
noncomputable def nb094AlphaDummy007 : Var :=
  (freshVar (((synCop (Class.cv (nb094AlphaDummy000))
          (Class.cv (nb094AlphaDummy001)))).fv ∪ ((Class.cv (nb094AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_008`. -/
@[expose]
noncomputable def nb094AlphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb094AlphaDummy003 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_009`. -/
@[expose]
noncomputable def nb094AlphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb094AlphaDummy003 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_010`. -/
@[expose]
noncomputable def nb094AlphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007)))))))).fv ∪ ((synCcompl
          (Class.cab (nb094AlphaDummy006)
            (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_011`. -/
@[expose]
noncomputable def nb094AlphaDummy011 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_012`. -/
@[expose]
noncomputable def nb094AlphaDummy012 : Var :=
  (freshVar (((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
            (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
            (Wff.classEq (Class.cv (nb094AlphaDummy006))
              (synCphi (Class.cv (nb094AlphaDummy007))))))).fv ∪
      ((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
            (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
            (Wff.classEq (Class.cv (nb094AlphaDummy006))
              (synCphi (Class.cv (nb094AlphaDummy007))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_013`. -/
@[expose]
noncomputable def nb094AlphaDummy013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb094AlphaDummy008 x y)
          (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
              (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv ∪
      ((Class.cab (nb094AlphaDummy008 x y)
          (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
              (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_014`. -/
@[expose]
noncomputable def nb094AlphaDummy014 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_015`. -/
@[expose]
noncomputable def nb094AlphaDummy015 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_016`. -/
@[expose]
noncomputable def nb094AlphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_017`. -/
@[expose]
noncomputable def nb094AlphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_018`. -/
@[expose]
noncomputable def nb094AlphaDummy018 : Var :=
  (freshVar (((synCcompl (Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCphi (Class.cv (nb094AlphaDummy015)))))))).fv ∪ ((synCcompl
          (Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_019`. -/
@[expose]
noncomputable def nb094AlphaDummy019 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCphi (Class.cv (nb094AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_020`. -/
@[expose]
noncomputable def nb094AlphaDummy020 : Var :=
  (freshVar (((Class.cab (nb094AlphaDummy014)
          (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
            (Wff.classEq (Class.cv (nb094AlphaDummy014))
              (synCphi (Class.cv (nb094AlphaDummy015))))))).fv ∪
      ((Class.cab (nb094AlphaDummy014)
          (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
            (Wff.classEq (Class.cv (nb094AlphaDummy014))
              (synCphi (Class.cv (nb094AlphaDummy015))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_021`. -/
@[expose]
noncomputable def nb094AlphaDummy021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb094AlphaDummy016 x y)
          (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
              (synCphi (Class.cv (nb094AlphaDummy017 x y))))))).fv ∪
      ((Class.cab (nb094AlphaDummy016 x y) (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
              (synCphi (Class.cv (nb094AlphaDummy017 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_022`. -/
@[expose]
noncomputable def nb094AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_023`. -/
@[expose]
noncomputable def nb094AlphaDummy023 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy015))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_024`. -/
@[expose]
noncomputable def nb094AlphaDummy024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy017 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_025`. -/
@[expose]
noncomputable def nb094AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy017 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_026`. -/
@[expose]
noncomputable def nb094AlphaDummy026 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb094AlphaDummy022)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb094AlphaDummy022)) (synC1c))).fv ∪
      ((Class.cv (nb094AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_027`. -/
@[expose]
noncomputable def nb094AlphaDummy027 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb094AlphaDummy024 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb094AlphaDummy024 x y)) (synC1c))).fv ∪
      ((Class.cv (nb094AlphaDummy024 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_028`. -/
@[expose]
noncomputable def nb094AlphaDummy028 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_029`. -/
@[expose]
noncomputable def nb094AlphaDummy029 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_030`. -/
@[expose]
noncomputable def nb094AlphaDummy030 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_031`. -/
@[expose]
noncomputable def nb094AlphaDummy031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_032`. -/
@[expose]
noncomputable def nb094AlphaDummy032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_033`. -/
@[expose]
noncomputable def nb094AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_034`. -/
@[expose]
noncomputable def nb094AlphaDummy034 : Var :=
  (freshVar (((synCnin (Class.cv (nb094AlphaDummy029))
          (Class.cv (nb094AlphaDummy030)))).fv ∪
      ((synCnin (Class.cv (nb094AlphaDummy029)) (Class.cv (nb094AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_035`. -/
@[expose]
noncomputable def nb094AlphaDummy035 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb094AlphaDummy032 x y))
          (Class.cv (nb094AlphaDummy033 x y)))).fv ∪
      ((synCnin (Class.cv (nb094AlphaDummy032 x y))
          (Class.cv (nb094AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_036`. -/
@[expose]
noncomputable def nb094AlphaDummy036 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_037`. -/
@[expose]
noncomputable def nb094AlphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb094AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_038`. -/
@[expose]
noncomputable def nb094AlphaDummy038 : Var :=
  (freshVar (((synCcompl (Class.cv (nb094AlphaDummy029)))).fv ∪
      ((synCcompl (Class.cv (nb094AlphaDummy030)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_039`. -/
@[expose]
noncomputable def nb094AlphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb094AlphaDummy032 x y)))).fv ∪
      ((synCcompl (Class.cv (nb094AlphaDummy033 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_040`. -/
@[expose]
noncomputable def nb094AlphaDummy040 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy029))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_041`. -/
@[expose]
noncomputable def nb094AlphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
      ((Class.cv (nb094AlphaDummy032 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_042`. -/
@[expose]
noncomputable def nb094AlphaDummy042 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy030))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_043`. -/
@[expose]
noncomputable def nb094AlphaDummy043 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy033 x y))).fv ∪
      ((Class.cv (nb094AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_044`. -/
@[expose]
noncomputable def nb094AlphaDummy044 : Var :=
  (freshVar (((Class.cab (nb094AlphaDummy014)
          (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
            (Wff.classEq (Class.cv (nb094AlphaDummy014))
              (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy014)
          (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
            (Wff.classEq (Class.cv (nb094AlphaDummy014))
              (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_045`. -/
@[expose]
noncomputable def nb094AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb094AlphaDummy016 x y)
          (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy016 x y)
          (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
              (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_046`. -/
@[expose]
noncomputable def nb094AlphaDummy046 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb094AlphaDummy015))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_047`. -/
@[expose]
noncomputable def nb094AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb094AlphaDummy017 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_048`. -/
@[expose]
noncomputable def nb094AlphaDummy048 : Var :=
  (freshVar (((synCphi (Class.cv (nb094AlphaDummy015)))).fv ∪
      ((synCphi (Class.cv (nb094AlphaDummy015)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_049`. -/
@[expose]
noncomputable def nb094AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb094AlphaDummy017 x y)))).fv ∪
      ((synCphi (Class.cv (nb094AlphaDummy017 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_050`. -/
@[expose]
noncomputable def nb094AlphaDummy050 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_051`. -/
@[expose]
noncomputable def nb094AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy007))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_052`. -/
@[expose]
noncomputable def nb094AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy009 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_053`. -/
@[expose]
noncomputable def nb094AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy009 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_054`. -/
@[expose]
noncomputable def nb094AlphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb094AlphaDummy050)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb094AlphaDummy050)) (synC1c))).fv ∪
      ((Class.cv (nb094AlphaDummy050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_055`. -/
@[expose]
noncomputable def nb094AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb094AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb094AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb094AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_056`. -/
@[expose]
noncomputable def nb094AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_057`. -/
@[expose]
noncomputable def nb094AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_058`. -/
@[expose]
noncomputable def nb094AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_059`. -/
@[expose]
noncomputable def nb094AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_060`. -/
@[expose]
noncomputable def nb094AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_061`. -/
@[expose]
noncomputable def nb094AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_062`. -/
@[expose]
noncomputable def nb094AlphaDummy062 : Var :=
  (freshVar (((synCnin (Class.cv (nb094AlphaDummy057))
          (Class.cv (nb094AlphaDummy058)))).fv ∪
      ((synCnin (Class.cv (nb094AlphaDummy057)) (Class.cv (nb094AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_063`. -/
@[expose]
noncomputable def nb094AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb094AlphaDummy060 x y))
          (Class.cv (nb094AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb094AlphaDummy060 x y))
          (Class.cv (nb094AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_064`. -/
@[expose]
noncomputable def nb094AlphaDummy064 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_065`. -/
@[expose]
noncomputable def nb094AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb094AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_066`. -/
@[expose]
noncomputable def nb094AlphaDummy066 : Var :=
  (freshVar (((synCcompl (Class.cv (nb094AlphaDummy057)))).fv ∪
      ((synCcompl (Class.cv (nb094AlphaDummy058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_067`. -/
@[expose]
noncomputable def nb094AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb094AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb094AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_068`. -/
@[expose]
noncomputable def nb094AlphaDummy068 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy057))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_069`. -/
@[expose]
noncomputable def nb094AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb094AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_070`. -/
@[expose]
noncomputable def nb094AlphaDummy070 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy058))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_071`. -/
@[expose]
noncomputable def nb094AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb094AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_072`. -/
@[expose]
noncomputable def nb094AlphaDummy072 : Var :=
  (freshVar (((Class.cab (nb094AlphaDummy006)
          (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
            (Wff.classEq (Class.cv (nb094AlphaDummy006))
              (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy006)
          (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
            (Wff.classEq (Class.cv (nb094AlphaDummy006))
              (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_073`. -/
@[expose]
noncomputable def nb094AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb094AlphaDummy008 x y)
          (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy008 x y)
          (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
            (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
              (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_074`. -/
@[expose]
noncomputable def nb094AlphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb094AlphaDummy007))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_075`. -/
@[expose]
noncomputable def nb094AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb094AlphaDummy009 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_076`. -/
@[expose]
noncomputable def nb094AlphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv (nb094AlphaDummy007)))).fv ∪
      ((synCphi (Class.cv (nb094AlphaDummy007)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_077`. -/
@[expose]
noncomputable def nb094AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb094AlphaDummy009 x y)))).fv ∪
      ((synCphi (Class.cv (nb094AlphaDummy009 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_078`. -/
@[expose]
noncomputable def nb094AlphaDummy078 : Var :=
  (freshVar (((synCnin (Class.cv (nb094AlphaDummy000))
          (synCcompl (Class.cv (nb094AlphaDummy001))))).fv ∪
      ((synCnin (Class.cv (nb094AlphaDummy000))
          (synCcompl (Class.cv (nb094AlphaDummy001))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_079`. -/
@[expose]
noncomputable def nb094AlphaDummy079 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv ∪
      ((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_080`. -/
@[expose]
noncomputable def nb094AlphaDummy080 : Var :=
  (freshVar (((Class.cv (nb094AlphaDummy000))).fv ∪
      ((synCcompl (Class.cv (nb094AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_081`. -/
@[expose]
noncomputable def nb094AlphaDummy081 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((synCcompl (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_082`. -/
@[expose]
noncomputable def nb094AlphaDummy082 : Var :=
  (freshVar
    (((Class.cv (nb094AlphaDummy001))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb094_alpha_dummy_083`. -/
@[expose]
noncomputable def nb094AlphaDummy083 (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0)

theorem nb094_fresh_000 :
    (nb094AlphaDummy072) ∉
      (((Class.cab (nb094AlphaDummy006)
            (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy006)
            (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb094AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb094AlphaDummy006)
            (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy006)
            (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb094_fresh_001 :
    (nb094AlphaDummy012) ∉
      (((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))).fv ∪
        ((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))).fv) :=
  by
  simpa only [nb094AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))).fv ∪
        ((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))).fv)
      0

theorem nb094_fresh_002 (x : Var) (y : Var) :
    (nb094AlphaDummy073 x y) ∉
      (((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb094AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb094_fresh_003 (x : Var) (y : Var) :
    (nb094AlphaDummy013 x y) ∉
      (((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv) :=
  by
  simpa only [nb094AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv)
      0

theorem nb094_fresh_004 :
    (nb094AlphaDummy020) ∉
      (((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCphi (Class.cv (nb094AlphaDummy015))))))).fv ∪
        ((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCphi (Class.cv (nb094AlphaDummy015))))))).fv) :=
  by
  simpa only [nb094AlphaDummy020] using
    freshVar_not_mem
      (((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCphi (Class.cv (nb094AlphaDummy015))))))).fv ∪
        ((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCphi (Class.cv (nb094AlphaDummy015))))))).fv)
      0

theorem nb094_fresh_005 :
    (nb094AlphaDummy044) ∉
      (((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb094AlphaDummy044] using
    freshVar_not_mem
      (((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb094_fresh_006 (x : Var) (y : Var) :
    (nb094AlphaDummy021 x y) ∉
      (((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCphi (Class.cv (nb094AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCphi (Class.cv (nb094AlphaDummy017 x y))))))).fv) :=
  by
  simpa only [nb094AlphaDummy021] using
    freshVar_not_mem
      (((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCphi (Class.cv (nb094AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCphi (Class.cv (nb094AlphaDummy017 x y))))))).fv)
      0

theorem nb094_fresh_007 (x : Var) (y : Var) :
    (nb094AlphaDummy045 x y) ∉
      (((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb094AlphaDummy045] using
    freshVar_not_mem
      (((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb094_fresh_008 :
    (nb094AlphaDummy014) ∉
      (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) :=
  by
  simpa only [nb094AlphaDummy014] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv)
      0

theorem nb094_fresh_009 :
    (nb094AlphaDummy015) ∉
      (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) :=
  by
  simpa only [nb094AlphaDummy015] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv)
      1

theorem nb094_distinct_010 : (nb094AlphaDummy014) ≠ (nb094AlphaDummy015) := by
  simpa only [nb094AlphaDummy014, nb094AlphaDummy015] using
    (freshVar_injective
      (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb094_fresh_011 :
    (nb094AlphaDummy080) ∉
      (((Class.cv (nb094AlphaDummy000))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy001)))).fv) :=
  by
  simpa only [nb094AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy000))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy001)))).fv)
      0

theorem nb094_fresh_012 :
    (nb094AlphaDummy082) ∉
      (((Class.cv (nb094AlphaDummy001))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) :=
  by
  simpa only [nb094AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy001))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv)
      0

theorem nb094_fresh_013 :
    (nb094AlphaDummy050) ∉ (((Class.cv (nb094AlphaDummy007))).fv) := by
  simpa only [nb094AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy007))).fv) 0

theorem nb094_fresh_014 :
    (nb094AlphaDummy051) ∉ (((Class.cv (nb094AlphaDummy007))).fv) := by
  simpa only [nb094AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy007))).fv) 1

theorem nb094_distinct_015 : (nb094AlphaDummy050) ≠ (nb094AlphaDummy051) := by
  simpa only [nb094AlphaDummy050, nb094AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy007))).fv) (i := 0) (j := 1) (by decide))

theorem nb094_fresh_016 (x : Var) (y : Var) :
    (nb094AlphaDummy052 x y) ∉ (((Class.cv (nb094AlphaDummy009 x y))).fv) := by
  simpa only [nb094AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy009 x y))).fv) 0

theorem nb094_fresh_017 (x : Var) (y : Var) :
    (nb094AlphaDummy053 x y) ∉ (((Class.cv (nb094AlphaDummy009 x y))).fv) := by
  simpa only [nb094AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy009 x y))).fv) 1

theorem nb094_distinct_018 (x : Var) (y : Var) :
    (nb094AlphaDummy052 x y) ≠ (nb094AlphaDummy053 x y) := by
  simpa only [nb094AlphaDummy052, nb094AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy009 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb094_fresh_019 :
    (nb094AlphaDummy022) ∉ (((Class.cv (nb094AlphaDummy015))).fv) := by
  simpa only [nb094AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy015))).fv) 0

theorem nb094_fresh_020 :
    (nb094AlphaDummy023) ∉ (((Class.cv (nb094AlphaDummy015))).fv) := by
  simpa only [nb094AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy015))).fv) 1

theorem nb094_distinct_021 : (nb094AlphaDummy022) ≠ (nb094AlphaDummy023) := by
  simpa only [nb094AlphaDummy022, nb094AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy015))).fv) (i := 0) (j := 1) (by decide))

theorem nb094_fresh_022 (x : Var) (y : Var) :
    (nb094AlphaDummy024 x y) ∉ (((Class.cv (nb094AlphaDummy017 x y))).fv) := by
  simpa only [nb094AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy017 x y))).fv) 0

theorem nb094_fresh_023 (x : Var) (y : Var) :
    (nb094AlphaDummy025 x y) ∉ (((Class.cv (nb094AlphaDummy017 x y))).fv) := by
  simpa only [nb094AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy017 x y))).fv) 1

theorem nb094_distinct_024 (x : Var) (y : Var) :
    (nb094AlphaDummy024 x y) ≠ (nb094AlphaDummy025 x y) := by
  simpa only [nb094AlphaDummy024, nb094AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy017 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb094_fresh_025 :
    (nb094AlphaDummy028) ∉
      (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) 0

theorem nb094_fresh_026 :
    (nb094AlphaDummy029) ∉
      (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) 1

theorem nb094_fresh_027 :
    (nb094AlphaDummy030) ∉
      (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) 2

theorem nb094_distinct_028 : (nb094AlphaDummy028) ≠ (nb094AlphaDummy029) := by
  simpa only [nb094AlphaDummy028, nb094AlphaDummy029] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb094_distinct_029 : (nb094AlphaDummy028) ≠ (nb094AlphaDummy030) := by
  simpa only [nb094AlphaDummy028, nb094AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb094_distinct_030 : (nb094AlphaDummy029) ≠ (nb094AlphaDummy030) := by
  simpa only [nb094AlphaDummy029, nb094AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb094_fresh_031 (x : Var) (y : Var) :
    (nb094AlphaDummy031 x y) ∉
      (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb094_fresh_032 (x : Var) (y : Var) :
    (nb094AlphaDummy032 x y) ∉
      (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb094_fresh_033 (x : Var) (y : Var) :
    (nb094AlphaDummy033 x y) ∉
      (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb094_distinct_034 (x : Var) (y : Var) :
    (nb094AlphaDummy031 x y) ≠ (nb094AlphaDummy032 x y) := by
  simpa only [nb094AlphaDummy031, nb094AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb094_distinct_035 (x : Var) (y : Var) :
    (nb094AlphaDummy031 x y) ≠ (nb094AlphaDummy033 x y) := by
  simpa only [nb094AlphaDummy031, nb094AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb094_distinct_036 (x : Var) (y : Var) :
    (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy033 x y) := by
  simpa only [nb094AlphaDummy032, nb094AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb094_fresh_037 :
    (nb094AlphaDummy040) ∉
      (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy029))).fv) :=
  by
  simpa only [nb094AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy029))).fv)
      0

theorem nb094_fresh_038 :
    (nb094AlphaDummy036) ∉
      (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv) :=
  by
  simpa only [nb094AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv)
      0

theorem nb094_fresh_039 :
    (nb094AlphaDummy042) ∉
      (((Class.cv (nb094AlphaDummy030))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv) :=
  by
  simpa only [nb094AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy030))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv)
      0

theorem nb094_fresh_040 (x : Var) (y : Var) :
    (nb094AlphaDummy041 x y) ∉
      (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy032 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy032 x y))).fv)
      0

theorem nb094_fresh_041 (x : Var) (y : Var) :
    (nb094AlphaDummy037 x y) ∉
      (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy033 x y))).fv)
      0

theorem nb094_fresh_042 (x : Var) (y : Var) :
    (nb094AlphaDummy043 x y) ∉
      (((Class.cv (nb094AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy033 x y))).fv)
      0

theorem nb094_fresh_043 :
    (nb094AlphaDummy056) ∉
      (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) 0

theorem nb094_fresh_044 :
    (nb094AlphaDummy057) ∉
      (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) 1

theorem nb094_fresh_045 :
    (nb094AlphaDummy058) ∉
      (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) 2

theorem nb094_distinct_046 : (nb094AlphaDummy056) ≠ (nb094AlphaDummy057) := by
  simpa only [nb094AlphaDummy056, nb094AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb094_distinct_047 : (nb094AlphaDummy056) ≠ (nb094AlphaDummy058) := by
  simpa only [nb094AlphaDummy056, nb094AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb094_distinct_048 : (nb094AlphaDummy057) ≠ (nb094AlphaDummy058) := by
  simpa only [nb094AlphaDummy057, nb094AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb094_fresh_049 (x : Var) (y : Var) :
    (nb094AlphaDummy059 x y) ∉
      (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb094_fresh_050 (x : Var) (y : Var) :
    (nb094AlphaDummy060 x y) ∉
      (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb094_fresh_051 (x : Var) (y : Var) :
    (nb094AlphaDummy061 x y) ∉
      (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb094AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb094_distinct_052 (x : Var) (y : Var) :
    (nb094AlphaDummy059 x y) ≠ (nb094AlphaDummy060 x y) := by
  simpa only [nb094AlphaDummy059, nb094AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb094_distinct_053 (x : Var) (y : Var) :
    (nb094AlphaDummy059 x y) ≠ (nb094AlphaDummy061 x y) := by
  simpa only [nb094AlphaDummy059, nb094AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb094_distinct_054 (x : Var) (y : Var) :
    (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy061 x y) := by
  simpa only [nb094AlphaDummy060, nb094AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb094_fresh_055 :
    (nb094AlphaDummy068) ∉
      (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy057))).fv) :=
  by
  simpa only [nb094AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy057))).fv)
      0

theorem nb094_fresh_056 :
    (nb094AlphaDummy064) ∉
      (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv) :=
  by
  simpa only [nb094AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv)
      0

theorem nb094_fresh_057 :
    (nb094AlphaDummy070) ∉
      (((Class.cv (nb094AlphaDummy058))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv) :=
  by
  simpa only [nb094AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy058))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv)
      0

theorem nb094_fresh_058 (x : Var) (y : Var) :
    (nb094AlphaDummy069 x y) ∉
      (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy060 x y))).fv)
      0

theorem nb094_fresh_059 (x : Var) (y : Var) :
    (nb094AlphaDummy065 x y) ∉
      (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy061 x y))).fv)
      0

theorem nb094_fresh_060 (x : Var) (y : Var) :
    (nb094AlphaDummy071 x y) ∉
      (((Class.cv (nb094AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb094AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy061 x y))).fv)
      0

theorem nb094_fresh_061 (x : Var) (y : Var) :
    (nb094AlphaDummy016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb094AlphaDummy016] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb094_fresh_062 (x : Var) (y : Var) :
    (nb094AlphaDummy017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb094AlphaDummy017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb094_distinct_063 (x : Var) (y : Var) :
    (nb094AlphaDummy016 x y) ≠ (nb094AlphaDummy017 x y) := by
  simpa only [nb094AlphaDummy016, nb094AlphaDummy017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb094_fresh_064 (x : Var) (y : Var) :
    (nb094AlphaDummy081 x y) ∉ (((Class.cv x)).fv ∪ ((synCcompl (Class.cv y))).fv) :=
  by
  simpa only [nb094AlphaDummy081] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((synCcompl (Class.cv y))).fv) 0

theorem nb094_fresh_065 (y : Var) :
    (nb094AlphaDummy083 y) ∉ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb094AlphaDummy083] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb094_fresh_066 :
    (nb094AlphaDummy026) ∉
      (((Wff.classMem (Class.cv (nb094AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy022))).fv) :=
  by
  simpa only [nb094AlphaDummy026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb094AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy022))).fv)
      0

theorem nb094_fresh_067 (x : Var) (y : Var) :
    (nb094AlphaDummy027 x y) ∉
      (((Wff.classMem (Class.cv (nb094AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy024 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb094AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy024 x y))).fv)
      0

theorem nb094_fresh_068 :
    (nb094AlphaDummy054) ∉
      (((Wff.classMem (Class.cv (nb094AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy050))).fv) :=
  by
  simpa only [nb094AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb094AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy050))).fv)
      0

theorem nb094_fresh_069 (x : Var) (y : Var) :
    (nb094AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb094AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb094AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy052 x y))).fv)
      0

theorem nb094_fresh_070 :
    (nb094AlphaDummy010) ∉
      (((synCcompl (Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
                (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCphi (Class.cv (nb094AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy006)
              (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb094AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
                (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCphi (Class.cv (nb094AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy006)
              (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb094_fresh_071 (x : Var) (y : Var) :
    (nb094AlphaDummy011 x y) ∉
      (((synCcompl (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCphi (Class.cv (nb094AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb094AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCphi (Class.cv (nb094AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb094_fresh_072 :
    (nb094AlphaDummy018) ∉
      (((synCcompl (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCphi (Class.cv (nb094AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb094AlphaDummy018] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCphi (Class.cv (nb094AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb094_fresh_073 (x : Var) (y : Var) :
    (nb094AlphaDummy019 x y) ∉
      (((synCcompl (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCphi (Class.cv (nb094AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb094AlphaDummy019] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCphi (Class.cv (nb094AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb094_fresh_074 :
    (nb094AlphaDummy038) ∉
      (((synCcompl (Class.cv (nb094AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy030)))).fv) :=
  by
  simpa only [nb094AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb094AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy030)))).fv)
      0

theorem nb094_fresh_075 (x : Var) (y : Var) :
    (nb094AlphaDummy039 x y) ∉
      (((synCcompl (Class.cv (nb094AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb094AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb094AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy033 x y)))).fv)
      0

theorem nb094_fresh_076 :
    (nb094AlphaDummy066) ∉
      (((synCcompl (Class.cv (nb094AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy058)))).fv) :=
  by
  simpa only [nb094AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb094AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy058)))).fv)
      0

theorem nb094_fresh_077 (x : Var) (y : Var) :
    (nb094AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb094AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb094AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb094AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy061 x y)))).fv)
      0

theorem nb094_fresh_078 :
    (nb094AlphaDummy074) ∉
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb094AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb094_fresh_079 (x : Var) (y : Var) :
    (nb094AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb094AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb094_fresh_080 :
    (nb094AlphaDummy046) ∉
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb094AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb094_fresh_081 (x : Var) (y : Var) :
    (nb094AlphaDummy047 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb094AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb094_fresh_082 :
    (nb094AlphaDummy078) ∉
      (((synCnin (Class.cv (nb094AlphaDummy000))
            (synCcompl (Class.cv (nb094AlphaDummy001))))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy000))
            (synCcompl (Class.cv (nb094AlphaDummy001))))).fv) :=
  by
  simpa only [nb094AlphaDummy078] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb094AlphaDummy000))
            (synCcompl (Class.cv (nb094AlphaDummy001))))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy000))
            (synCcompl (Class.cv (nb094AlphaDummy001))))).fv)
      0

theorem nb094_fresh_083 :
    (nb094AlphaDummy034) ∉
      (((synCnin (Class.cv (nb094AlphaDummy029)) (Class.cv (nb094AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy029))
            (Class.cv (nb094AlphaDummy030)))).fv) :=
  by
  simpa only [nb094AlphaDummy034] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb094AlphaDummy029)) (Class.cv (nb094AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy029)) (Class.cv (nb094AlphaDummy030)))).fv)
      0

theorem nb094_fresh_084 (x : Var) (y : Var) :
    (nb094AlphaDummy035 x y) ∉
      (((synCnin (Class.cv (nb094AlphaDummy032 x y))
            (Class.cv (nb094AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy032 x y))
            (Class.cv (nb094AlphaDummy033 x y)))).fv) :=
  by
  simpa only [nb094AlphaDummy035] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb094AlphaDummy032 x y))
            (Class.cv (nb094AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy032 x y))
            (Class.cv (nb094AlphaDummy033 x y)))).fv)
      0

theorem nb094_fresh_085 :
    (nb094AlphaDummy062) ∉
      (((synCnin (Class.cv (nb094AlphaDummy057)) (Class.cv (nb094AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy057))
            (Class.cv (nb094AlphaDummy058)))).fv) :=
  by
  simpa only [nb094AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb094AlphaDummy057)) (Class.cv (nb094AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy057)) (Class.cv (nb094AlphaDummy058)))).fv)
      0

theorem nb094_fresh_086 (x : Var) (y : Var) :
    (nb094AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb094AlphaDummy060 x y))
            (Class.cv (nb094AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy060 x y))
            (Class.cv (nb094AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb094AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb094AlphaDummy060 x y))
            (Class.cv (nb094AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy060 x y))
            (Class.cv (nb094AlphaDummy061 x y)))).fv)
      0

theorem nb094_fresh_087 (x : Var) (y : Var) :
    (nb094AlphaDummy079 x y) ∉
      (((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv ∪
        ((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv) :=
  by
  simpa only [nb094AlphaDummy079] using
    freshVar_not_mem
      (((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv ∪
        ((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv)
      0

theorem nb094_fresh_088 :
    (nb094AlphaDummy006) ∉
      (((synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv ∪
        ((Class.cv (nb094AlphaDummy002))).fv) :=
  by
  simpa only [nb094AlphaDummy006] using
    freshVar_not_mem
      (((synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv ∪
        ((Class.cv (nb094AlphaDummy002))).fv)
      0

theorem nb094_fresh_089 :
    (nb094AlphaDummy007) ∉
      (((synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv ∪
        ((Class.cv (nb094AlphaDummy002))).fv) :=
  by
  simpa only [nb094AlphaDummy007] using
    freshVar_not_mem
      (((synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv ∪
        ((Class.cv (nb094AlphaDummy002))).fv)
      1

theorem nb094_distinct_090 : (nb094AlphaDummy006) ≠ (nb094AlphaDummy007) := by
  simpa only [nb094AlphaDummy006, nb094AlphaDummy007] using
    (freshVar_injective (((synCop (Class.cv (nb094AlphaDummy000))
            (Class.cv (nb094AlphaDummy001)))).fv ∪ ((Class.cv (nb094AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb094_fresh_091 (x : Var) (y : Var) :
    (nb094AlphaDummy008 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb094AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy008] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb094AlphaDummy003 x y))).fv)
      0

theorem nb094_fresh_092 (x : Var) (y : Var) :
    (nb094AlphaDummy009 x y) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb094AlphaDummy003 x y))).fv) :=
  by
  simpa only [nb094AlphaDummy009] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb094AlphaDummy003 x y))).fv)
      1

theorem nb094_distinct_093 (x : Var) (y : Var) :
    (nb094AlphaDummy008 x y) ≠ (nb094AlphaDummy009 x y) := by
  simpa only [nb094AlphaDummy008, nb094AlphaDummy009] using
    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb094AlphaDummy003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb094_fresh_094 :
    (nb094AlphaDummy076) ∉
      (((synCphi (Class.cv (nb094AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy007)))).fv) :=
  by
  simpa only [nb094AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb094AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy007)))).fv)
      0

theorem nb094_fresh_095 (x : Var) (y : Var) :
    (nb094AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb094AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy009 x y)))).fv) :=
  by
  simpa only [nb094AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb094AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy009 x y)))).fv)
      0

theorem nb094_fresh_096 :
    (nb094AlphaDummy048) ∉
      (((synCphi (Class.cv (nb094AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy015)))).fv) :=
  by
  simpa only [nb094AlphaDummy048] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb094AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy015)))).fv)
      0

theorem nb094_fresh_097 (x : Var) (y : Var) :
    (nb094AlphaDummy049 x y) ∉
      (((synCphi (Class.cv (nb094AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy017 x y)))).fv) :=
  by
  simpa only [nb094AlphaDummy049] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb094AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy017 x y)))).fv)
      0

theorem nb094_fresh_098 :
    (nb094AlphaDummy002) ∉
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb094AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdif (Class.cv (nb094AlphaDummy000))
            (Class.cv (nb094AlphaDummy001)))).fv) :=
  by
  simpa only [nb094AlphaDummy002] using
    freshVar_not_mem
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb094AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdif (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv)
      0

theorem nb094_fresh_099 :
    (nb094AlphaDummy004) ∉
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ({(nb094AlphaDummy001)} : Finset Var) ∪
          ({(nb094AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb094AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb094AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy002))
              (synCdif (Class.cv (nb094AlphaDummy000))
                (Class.cv (nb094AlphaDummy001)))))).fv) :=
  by
  simpa only [nb094AlphaDummy004] using
    freshVar_not_mem
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ({(nb094AlphaDummy001)} : Finset Var) ∪
          ({(nb094AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb094AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb094AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy002))
              (synCdif (Class.cv (nb094AlphaDummy000))
                (Class.cv (nb094AlphaDummy001)))))).fv)
      0

theorem nb094_fresh_100 (x : Var) (y : Var) :
    (nb094AlphaDummy003 x y) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdif (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb094AlphaDummy003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdif (Class.cv x) (Class.cv y))).fv)
      0

theorem nb094_fresh_101 (x : Var) (y : Var) :
    (nb094AlphaDummy005 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb094AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy003 x y))
              (synCdif (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb094AlphaDummy005] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb094AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy003 x y))
              (synCdif (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb094_fresh_102 : (nb094AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb094AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb094_fresh_103 : (nb094AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb094AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb094_distinct_104 : (nb094AlphaDummy000) ≠ (nb094AlphaDummy001) := by
  simpa only [nb094AlphaDummy000, nb094AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb094_support_mem_0000 :
    (nb094AlphaDummy000) ∈
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ({(nb094AlphaDummy001)} : Finset Var) ∪
          ({(nb094AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb094AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb094AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy002))
              (synCdif (Class.cv (nb094AlphaDummy000))
                (Class.cv (nb094AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb094AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy003 x y))
              (synCdif (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0002 :
    (nb094AlphaDummy001) ∈
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ({(nb094AlphaDummy001)} : Finset Var) ∪
          ({(nb094AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb094AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb094AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy002))
              (synCdif (Class.cv (nb094AlphaDummy000))
                (Class.cv (nb094AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb094AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy003 x y))
              (synCdif (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0004 :
    (nb094AlphaDummy002) ∈
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ({(nb094AlphaDummy001)} : Finset Var) ∪
          ({(nb094AlphaDummy002)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb094AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb094AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy002))
              (synCdif (Class.cv (nb094AlphaDummy000))
                (Class.cv (nb094AlphaDummy001)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0005 (x : Var) (y : Var) :
    (nb094AlphaDummy003 x y) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb094AlphaDummy003 x y)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb094AlphaDummy003 x y))
              (synCdif (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0006 :
    (nb094AlphaDummy000) ∈
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb094AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdif (Class.cv (nb094AlphaDummy000))
            (Class.cv (nb094AlphaDummy001)))).fv) :=
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

theorem nb094_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdif (Class.cv x) (Class.cv y))).fv) :=
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

theorem nb094_support_mem_0008 :
    (nb094AlphaDummy000) ∈
      (((synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv ∪
        ((Class.cv (nb094AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0009 :
    (nb094AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
                (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCphi (Class.cv (nb094AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy006)
              (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy006) from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy007) from (by
            unfold nb094AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0010 (x : Var) (y : Var) :
    x ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb094AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0011 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCphi (Class.cv (nb094AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0010 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb094AlphaDummy009 x y) from (by
            unfold nb094AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0010 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0012 :
    (nb094AlphaDummy000) ∈
      (((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))).fv ∪
        ((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy006) from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy007) from (by
            unfold nb094AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0010 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb094AlphaDummy009 x y) from (by
            unfold nb094AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0010 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0014 :
    (nb094AlphaDummy000) ∈
      (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0015 :
    (nb094AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCphi (Class.cv (nb094AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy014) from (by
          unfold nb094AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy015) from (by
            unfold nb094AlphaDummy015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCphi (Class.cv (nb094AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb094AlphaDummy016 x y) from (by
          unfold nb094AlphaDummy016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0016 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb094AlphaDummy017 x y) from (by
            unfold nb094AlphaDummy017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0016 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0018 :
    (nb094AlphaDummy000) ∈
      (((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCphi (Class.cv (nb094AlphaDummy015))))))).fv ∪
        ((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCphi (Class.cv (nb094AlphaDummy015))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy014) from (by
          unfold nb094AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy015) from (by
            unfold nb094AlphaDummy015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCphi (Class.cv (nb094AlphaDummy017 x y))))))).fv ∪
        ((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCphi (Class.cv (nb094AlphaDummy017 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb094AlphaDummy016 x y) from (by
          unfold nb094AlphaDummy016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0016 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb094AlphaDummy017 x y) from (by
            unfold nb094AlphaDummy017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0016 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0020 :
    (nb094AlphaDummy015) ∈ (((Class.cv (nb094AlphaDummy015))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0021 (x : Var) (y : Var) :
    (nb094AlphaDummy017 x y) ∈ (((Class.cv (nb094AlphaDummy017 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0022 :
    (nb094AlphaDummy022) ∈
      (((Wff.classMem (Class.cv (nb094AlphaDummy022)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy022)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy022))).fv) :=
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

theorem nb094_support_mem_0023 (x : Var) (y : Var) :
    (nb094AlphaDummy024 x y) ∈
      (((Wff.classMem (Class.cv (nb094AlphaDummy024 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy024 x y)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy024 x y))).fv) :=
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

theorem nb094_support_mem_0024 :
    (nb094AlphaDummy022) ∈
      (((Class.cv (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0025 (x : Var) (y : Var) :
    (nb094AlphaDummy024 x y) ∈
      (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0026 :
    (nb094AlphaDummy029) ∈
      (((synCnin (Class.cv (nb094AlphaDummy029)) (Class.cv (nb094AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy029))
            (Class.cv (nb094AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0027 (x : Var) (y : Var) :
    (nb094AlphaDummy032 x y) ∈
      (((synCnin (Class.cv (nb094AlphaDummy032 x y))
            (Class.cv (nb094AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy032 x y))
            (Class.cv (nb094AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0028 :
    (nb094AlphaDummy029) ∈
      (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0029 (x : Var) (y : Var) :
    (nb094AlphaDummy032 x y) ∈
      (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0030 :
    (nb094AlphaDummy030) ∈
      (((synCnin (Class.cv (nb094AlphaDummy029)) (Class.cv (nb094AlphaDummy030)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy029))
            (Class.cv (nb094AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0031 (x : Var) (y : Var) :
    (nb094AlphaDummy033 x y) ∈
      (((synCnin (Class.cv (nb094AlphaDummy032 x y))
            (Class.cv (nb094AlphaDummy033 x y)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy032 x y))
            (Class.cv (nb094AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0032 :
    (nb094AlphaDummy030) ∈
      (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0033 (x : Var) (y : Var) :
    (nb094AlphaDummy033 x y) ∈
      (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0034 :
    (nb094AlphaDummy029) ∈
      (((synCcompl (Class.cv (nb094AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0035 (x : Var) (y : Var) :
    (nb094AlphaDummy032 x y) ∈
      (((synCcompl (Class.cv (nb094AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0036 :
    (nb094AlphaDummy029) ∈
      (((Class.cv (nb094AlphaDummy029))).fv ∪ ((Class.cv (nb094AlphaDummy029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0037 (x : Var) (y : Var) :
    (nb094AlphaDummy032 x y) ∈
      (((Class.cv (nb094AlphaDummy032 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy032 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0038 :
    (nb094AlphaDummy030) ∈
      (((synCcompl (Class.cv (nb094AlphaDummy029)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy030)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0039 (x : Var) (y : Var) :
    (nb094AlphaDummy033 x y) ∈
      (((synCcompl (Class.cv (nb094AlphaDummy032 x y)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy033 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0040 :
    (nb094AlphaDummy030) ∈
      (((Class.cv (nb094AlphaDummy030))).fv ∪ ((Class.cv (nb094AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0041 (x : Var) (y : Var) :
    (nb094AlphaDummy033 x y) ∈
      (((Class.cv (nb094AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0042 :
    (nb094AlphaDummy001) ∈
      (({(nb094AlphaDummy000)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb094AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdif (Class.cv (nb094AlphaDummy000))
            (Class.cv (nb094AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0043 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((synCdif (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0044 :
    (nb094AlphaDummy001) ∈
      (((synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv ∪
        ((Class.cv (nb094AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0045 :
    (nb094AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
                (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCphi (Class.cv (nb094AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy006)
              (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy006) from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy007) from (by
            unfold nb094AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0046 (x : Var) (y : Var) :
    y ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb094AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCphi (Class.cv (nb094AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0046 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb094AlphaDummy009 x y) from (by
            unfold nb094AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0046 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0048 :
    (nb094AlphaDummy001) ∈
      (((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))).fv ∪
        ((Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy006) from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy007) from (by
            unfold nb094AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0049 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv ∪
        ((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0046 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb094AlphaDummy009 x y) from (by
            unfold nb094AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0046 x y) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0050 :
    (nb094AlphaDummy001) ∈
      (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0051 :
    (nb094AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCphi (Class.cv (nb094AlphaDummy015)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy014) from (by
          unfold nb094AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy015) from (by
            unfold nb094AlphaDummy015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCphi (Class.cv (nb094AlphaDummy017 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb094AlphaDummy016 x y) from (by
          unfold nb094AlphaDummy016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0052 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb094AlphaDummy017 x y) from (by
            unfold nb094AlphaDummy017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0052 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0054 :
    (nb094AlphaDummy001) ∈
      (((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy001))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCun (synCphi (Class.cv (nb094AlphaDummy015)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy014) from (by
          unfold nb094AlphaDummy014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy015) from (by
            unfold nb094AlphaDummy015;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy017 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb094AlphaDummy016 x y) from (by
          unfold nb094AlphaDummy016;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0052 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb094AlphaDummy017 x y) from (by
            unfold nb094AlphaDummy017;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0052 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0056 :
    (nb094AlphaDummy015) ∈
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy015))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0057 (x : Var) (y : Var) :
    (nb094AlphaDummy017 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy017 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0058 :
    (nb094AlphaDummy015) ∈
      (((synCphi (Class.cv (nb094AlphaDummy015)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy015)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0059 (x : Var) (y : Var) :
    (nb094AlphaDummy017 x y) ∈
      (((synCphi (Class.cv (nb094AlphaDummy017 x y)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy017 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0060 :
    (nb094AlphaDummy007) ∈ (((Class.cv (nb094AlphaDummy007))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0061 (x : Var) (y : Var) :
    (nb094AlphaDummy009 x y) ∈ (((Class.cv (nb094AlphaDummy009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0062 :
    (nb094AlphaDummy050) ∈
      (((Wff.classMem (Class.cv (nb094AlphaDummy050)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy050)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy050))).fv) :=
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

theorem nb094_support_mem_0063 (x : Var) (y : Var) :
    (nb094AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb094AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb094AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb094AlphaDummy052 x y))).fv) :=
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

theorem nb094_support_mem_0064 :
    (nb094AlphaDummy050) ∈
      (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0065 (x : Var) (y : Var) :
    (nb094AlphaDummy052 x y) ∈
      (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0066 :
    (nb094AlphaDummy057) ∈
      (((synCnin (Class.cv (nb094AlphaDummy057)) (Class.cv (nb094AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy057))
            (Class.cv (nb094AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0067 (x : Var) (y : Var) :
    (nb094AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb094AlphaDummy060 x y))
            (Class.cv (nb094AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy060 x y))
            (Class.cv (nb094AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0068 :
    (nb094AlphaDummy057) ∈
      (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0069 (x : Var) (y : Var) :
    (nb094AlphaDummy060 x y) ∈
      (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0070 :
    (nb094AlphaDummy058) ∈
      (((synCnin (Class.cv (nb094AlphaDummy057)) (Class.cv (nb094AlphaDummy058)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy057))
            (Class.cv (nb094AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0071 (x : Var) (y : Var) :
    (nb094AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb094AlphaDummy060 x y))
            (Class.cv (nb094AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy060 x y))
            (Class.cv (nb094AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0072 :
    (nb094AlphaDummy058) ∈
      (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0073 (x : Var) (y : Var) :
    (nb094AlphaDummy061 x y) ∈
      (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0074 :
    (nb094AlphaDummy057) ∈
      (((synCcompl (Class.cv (nb094AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0075 (x : Var) (y : Var) :
    (nb094AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb094AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0076 :
    (nb094AlphaDummy057) ∈
      (((Class.cv (nb094AlphaDummy057))).fv ∪ ((Class.cv (nb094AlphaDummy057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0077 (x : Var) (y : Var) :
    (nb094AlphaDummy060 x y) ∈
      (((Class.cv (nb094AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0078 :
    (nb094AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb094AlphaDummy057)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0079 (x : Var) (y : Var) :
    (nb094AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb094AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0080 :
    (nb094AlphaDummy058) ∈
      (((Class.cv (nb094AlphaDummy058))).fv ∪ ((Class.cv (nb094AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0081 (x : Var) (y : Var) :
    (nb094AlphaDummy061 x y) ∈
      (((Class.cv (nb094AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb094AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0082 :
    (nb094AlphaDummy002) ∈
      (((synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))).fv ∪
        ((Class.cv (nb094AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0083 :
    (nb094AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
                (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCphi (Class.cv (nb094AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy006)
              (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy006) from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy007) from (by
            unfold nb094AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0084 (x : Var) (y : Var) :
    (nb094AlphaDummy003 x y) ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb094AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0085 (x : Var) (y : Var) :
    (nb094AlphaDummy003 x y) ∈
      (((synCcompl (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCphi (Class.cv (nb094AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0084 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy009 x y) from (by
            unfold nb094AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0084 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0086 :
    (nb094AlphaDummy002) ∈
      (((Class.cab (nb094AlphaDummy006)
            (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy006)
            (synWrex (nb094AlphaDummy007) (Class.cv (nb094AlphaDummy002))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCun (synCphi (Class.cv (nb094AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy006) from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy007) from (by
            unfold nb094AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb094_support_mem_0087 (x : Var) (y : Var) :
    (nb094AlphaDummy003 x y) ∈
      (((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (Class.cv (nb094AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0084 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy009 x y) from (by
            unfold nb094AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0084 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb094_support_mem_0088 :
    (nb094AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0089 (x : Var) (y : Var) :
    (nb094AlphaDummy009 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb094AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0090 :
    (nb094AlphaDummy007) ∈
      (((synCphi (Class.cv (nb094AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0091 (x : Var) (y : Var) :
    (nb094AlphaDummy009 x y) ∈
      (((synCphi (Class.cv (nb094AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb094AlphaDummy009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0092 :
    (nb094AlphaDummy000) ∈
      (((synCnin (Class.cv (nb094AlphaDummy000))
            (synCcompl (Class.cv (nb094AlphaDummy001))))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy000))
            (synCcompl (Class.cv (nb094AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0093 (x : Var) (y : Var) :
    x ∈
      (((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv ∪
        ((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0094 :
    (nb094AlphaDummy000) ∈
      (((Class.cv (nb094AlphaDummy000))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0095 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((synCcompl (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0096 :
    (nb094AlphaDummy001) ∈
      (((synCnin (Class.cv (nb094AlphaDummy000))
            (synCcompl (Class.cv (nb094AlphaDummy001))))).fv ∪
        ((synCnin (Class.cv (nb094AlphaDummy000))
            (synCcompl (Class.cv (nb094AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0097 (x : Var) (y : Var) :
    y ∈
      (((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv ∪
        ((synCnin (Class.cv x) (synCcompl (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0098 :
    (nb094AlphaDummy001) ∈
      (((Class.cv (nb094AlphaDummy000))).fv ∪
        ((synCcompl (Class.cv (nb094AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0099 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((synCcompl (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0100 :
    (nb094AlphaDummy001) ∈
      (((Class.cv (nb094AlphaDummy001))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb094_support_mem_0101 (y : Var) : y ∈ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
