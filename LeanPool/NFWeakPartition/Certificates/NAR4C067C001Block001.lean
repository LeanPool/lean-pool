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

/-! Certificates from `NAR4C067C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_000`. -/
@[expose]
noncomputable def nb067AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_001`. -/
@[expose]
noncomputable def nb067AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_002`. -/
@[expose]
noncomputable def nb067AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_003`. -/
@[expose]
noncomputable def nb067AlphaDummy003 : Var :=
  (freshVar (({(nb067AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
          ({(nb067AlphaDummy002)} : Finset Var) ∪ ((synCvv)).fv ∪
      ((Class.cab (nb067AlphaDummy000)
          (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
            (Class.cv (nb067AlphaDummy001))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_004`. -/
@[expose]
noncomputable def nb067AlphaDummy004 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
      ((Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_005`. -/
@[expose]
noncomputable def nb067AlphaDummy005 : Var :=
  (freshVar
    (({(nb067AlphaDummy001)} : Finset Var) ∪ ({(nb067AlphaDummy002)} : Finset Var) ∪
        ({(nb067AlphaDummy003)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv (nb067AlphaDummy001)) (synCvv))
            (Wff.classMem (Class.cv (nb067AlphaDummy002)) (synCvv)))
          (Wff.classEq (Class.cv (nb067AlphaDummy003)) (Class.cab (nb067AlphaDummy000)
              (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
                (Class.cv (nb067AlphaDummy001))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_006`. -/
@[expose]
noncomputable def nb067AlphaDummy006 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ({(nb067AlphaDummy004 x y f)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
          (Wff.classEq (Class.cv (nb067AlphaDummy004 x y f))
            (Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_007`. -/
@[expose]
noncomputable def nb067AlphaDummy007 : Var :=
  (freshVar (((synCop (Class.cv (nb067AlphaDummy001))
          (Class.cv (nb067AlphaDummy002)))).fv ∪ ((Class.cv (nb067AlphaDummy003))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_008`. -/
@[expose]
noncomputable def nb067AlphaDummy008 : Var :=
  (freshVar (((synCop (Class.cv (nb067AlphaDummy001))
          (Class.cv (nb067AlphaDummy002)))).fv ∪ ((Class.cv (nb067AlphaDummy003))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_009`. -/
@[expose]
noncomputable def nb067AlphaDummy009 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb067AlphaDummy004 x y f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_010`. -/
@[expose]
noncomputable def nb067AlphaDummy010 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((synCop (Class.cv x) (Class.cv y))).fv ∪
      ((Class.cv (nb067AlphaDummy004 x y f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_011`. -/
@[expose]
noncomputable def nb067AlphaDummy011 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy007)
            (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_012`. -/
@[expose]
noncomputable def nb067AlphaDummy012 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
              (Class.cv (nb067AlphaDummy004 x y f))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_013`. -/
@[expose]
noncomputable def nb067AlphaDummy013 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
            (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
            (Wff.classEq (Class.cv (nb067AlphaDummy007))
              (synCphi (Class.cv (nb067AlphaDummy008))))))).fv ∪
      ((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
            (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
            (Wff.classEq (Class.cv (nb067AlphaDummy007))
              (synCphi (Class.cv (nb067AlphaDummy008))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_014`. -/
@[expose]
noncomputable def nb067AlphaDummy014 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy009 x y f)
          (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
              (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv ∪
      ((Class.cab (nb067AlphaDummy009 x y f)
          (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
            (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
              (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_015`. -/
@[expose]
noncomputable def nb067AlphaDummy015 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_016`. -/
@[expose]
noncomputable def nb067AlphaDummy016 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_017`. -/
@[expose]
noncomputable def nb067AlphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_018`. -/
@[expose]
noncomputable def nb067AlphaDummy018 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_019`. -/
@[expose]
noncomputable def nb067AlphaDummy019 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCphi (Class.cv (nb067AlphaDummy016)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_020`. -/
@[expose]
noncomputable def nb067AlphaDummy020 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCphi (Class.cv (nb067AlphaDummy018 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_021`. -/
@[expose]
noncomputable def nb067AlphaDummy021 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy015)
          (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
            (Wff.classEq (Class.cv (nb067AlphaDummy015))
              (synCphi (Class.cv (nb067AlphaDummy016))))))).fv ∪
      ((Class.cab (nb067AlphaDummy015)
          (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
            (Wff.classEq (Class.cv (nb067AlphaDummy015))
              (synCphi (Class.cv (nb067AlphaDummy016))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_022`. -/
@[expose]
noncomputable def nb067AlphaDummy022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy017 x y)
          (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
              (synCphi (Class.cv (nb067AlphaDummy018 x y))))))).fv ∪
      ((Class.cab (nb067AlphaDummy017 x y) (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
              (synCphi (Class.cv (nb067AlphaDummy018 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_023`. -/
@[expose]
noncomputable def nb067AlphaDummy023 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy016))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_024`. -/
@[expose]
noncomputable def nb067AlphaDummy024 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy016))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_025`. -/
@[expose]
noncomputable def nb067AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy018 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_026`. -/
@[expose]
noncomputable def nb067AlphaDummy026 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy018 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_027`. -/
@[expose]
noncomputable def nb067AlphaDummy027 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy023)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy023)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy023))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_028`. -/
@[expose]
noncomputable def nb067AlphaDummy028 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy025 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy025 x y)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy025 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_029`. -/
@[expose]
noncomputable def nb067AlphaDummy029 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_030`. -/
@[expose]
noncomputable def nb067AlphaDummy030 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_031`. -/
@[expose]
noncomputable def nb067AlphaDummy031 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_032`. -/
@[expose]
noncomputable def nb067AlphaDummy032 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_033`. -/
@[expose]
noncomputable def nb067AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_034`. -/
@[expose]
noncomputable def nb067AlphaDummy034 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_035`. -/
@[expose]
noncomputable def nb067AlphaDummy035 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy030))
          (Class.cv (nb067AlphaDummy031)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_036`. -/
@[expose]
noncomputable def nb067AlphaDummy036 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy033 x y))
          (Class.cv (nb067AlphaDummy034 x y)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy033 x y))
          (Class.cv (nb067AlphaDummy034 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_037`. -/
@[expose]
noncomputable def nb067AlphaDummy037 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_038`. -/
@[expose]
noncomputable def nb067AlphaDummy038 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
      ((Class.cv (nb067AlphaDummy034 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_039`. -/
@[expose]
noncomputable def nb067AlphaDummy039 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy030)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy031)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_040`. -/
@[expose]
noncomputable def nb067AlphaDummy040 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy033 x y)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy034 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_041`. -/
@[expose]
noncomputable def nb067AlphaDummy041 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy030))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_042`. -/
@[expose]
noncomputable def nb067AlphaDummy042 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
      ((Class.cv (nb067AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_043`. -/
@[expose]
noncomputable def nb067AlphaDummy043 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy031))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_044`. -/
@[expose]
noncomputable def nb067AlphaDummy044 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy034 x y))).fv ∪
      ((Class.cv (nb067AlphaDummy034 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_045`. -/
@[expose]
noncomputable def nb067AlphaDummy045 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy015)
          (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
            (Wff.classEq (Class.cv (nb067AlphaDummy015))
              (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy015)
          (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
            (Wff.classEq (Class.cv (nb067AlphaDummy015))
              (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_046`. -/
@[expose]
noncomputable def nb067AlphaDummy046 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy017 x y)
          (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
              (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy017 x y)
          (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
              (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_047`. -/
@[expose]
noncomputable def nb067AlphaDummy047 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy016))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_048`. -/
@[expose]
noncomputable def nb067AlphaDummy048 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy018 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_049`. -/
@[expose]
noncomputable def nb067AlphaDummy049 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy016)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy016)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_050`. -/
@[expose]
noncomputable def nb067AlphaDummy050 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy018 x y)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy018 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_051`. -/
@[expose]
noncomputable def nb067AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy008))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_052`. -/
@[expose]
noncomputable def nb067AlphaDummy052 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy008))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_053`. -/
@[expose]
noncomputable def nb067AlphaDummy053 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy010 x y f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_054`. -/
@[expose]
noncomputable def nb067AlphaDummy054 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy010 x y f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_055`. -/
@[expose]
noncomputable def nb067AlphaDummy055 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy051)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy051)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy051))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_056`. -/
@[expose]
noncomputable def nb067AlphaDummy056 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy053 x y f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy053 x y f)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy053 x y f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_057`. -/
@[expose]
noncomputable def nb067AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_058`. -/
@[expose]
noncomputable def nb067AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_059`. -/
@[expose]
noncomputable def nb067AlphaDummy059 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_060`. -/
@[expose]
noncomputable def nb067AlphaDummy060 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_061`. -/
@[expose]
noncomputable def nb067AlphaDummy061 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_062`. -/
@[expose]
noncomputable def nb067AlphaDummy062 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_063`. -/
@[expose]
noncomputable def nb067AlphaDummy063 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy058))
          (Class.cv (nb067AlphaDummy059)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_064`. -/
@[expose]
noncomputable def nb067AlphaDummy064 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy061 x y f))
          (Class.cv (nb067AlphaDummy062 x y f)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy061 x y f))
          (Class.cv (nb067AlphaDummy062 x y f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_065`. -/
@[expose]
noncomputable def nb067AlphaDummy065 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_066`. -/
@[expose]
noncomputable def nb067AlphaDummy066 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
      ((Class.cv (nb067AlphaDummy062 x y f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_067`. -/
@[expose]
noncomputable def nb067AlphaDummy067 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy058)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy059)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_068`. -/
@[expose]
noncomputable def nb067AlphaDummy068 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy061 x y f)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy062 x y f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_069`. -/
@[expose]
noncomputable def nb067AlphaDummy069 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_070`. -/
@[expose]
noncomputable def nb067AlphaDummy070 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
      ((Class.cv (nb067AlphaDummy061 x y f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_071`. -/
@[expose]
noncomputable def nb067AlphaDummy071 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy059))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_072`. -/
@[expose]
noncomputable def nb067AlphaDummy072 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy062 x y f))).fv ∪
      ((Class.cv (nb067AlphaDummy062 x y f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_073`. -/
@[expose]
noncomputable def nb067AlphaDummy073 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy007)
          (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
            (Wff.classEq (Class.cv (nb067AlphaDummy007))
              (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy007)
          (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
            (Wff.classEq (Class.cv (nb067AlphaDummy007))
              (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_074`. -/
@[expose]
noncomputable def nb067AlphaDummy074 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy009 x y f)
          (synWrex (nb067AlphaDummy010 x y f) (Class.cv (nb067AlphaDummy004 x y f))
            (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy009 x y f)
          (synWrex (nb067AlphaDummy010 x y f) (Class.cv (nb067AlphaDummy004 x y f))
            (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_075`. -/
@[expose]
noncomputable def nb067AlphaDummy075 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy008))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_076`. -/
@[expose]
noncomputable def nb067AlphaDummy076 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy010 x y f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_077`. -/
@[expose]
noncomputable def nb067AlphaDummy077 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy008)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy008)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_078`. -/
@[expose]
noncomputable def nb067AlphaDummy078 (x : Var) (y : Var) (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy010 x y f)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy010 x y f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_079`. -/
@[expose]
noncomputable def nb067AlphaDummy079 : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb067AlphaDummy000))
            (synCcnv (Class.cv (nb067AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
          (synCcom (Class.cv (nb067AlphaDummy000))
            (synCcnv (Class.cv (nb067AlphaDummy000)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_080`. -/
@[expose]
noncomputable def nb067AlphaDummy080 (f : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_081`. -/
@[expose]
noncomputable def nb067AlphaDummy081 : Var :=
  (freshVar (((synCcom (Class.cv (nb067AlphaDummy000))
          (synCcnv (Class.cv (nb067AlphaDummy000))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_082`. -/
@[expose]
noncomputable def nb067AlphaDummy082 (f : Var) : Var :=
  (freshVar (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_083`. -/
@[expose]
noncomputable def nb067AlphaDummy083 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_084`. -/
@[expose]
noncomputable def nb067AlphaDummy084 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_085`. -/
@[expose]
noncomputable def nb067AlphaDummy085 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy000))).fv ∪
      ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_086`. -/
@[expose]
noncomputable def nb067AlphaDummy086 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_087`. -/
@[expose]
noncomputable def nb067AlphaDummy087 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_088`. -/
@[expose]
noncomputable def nb067AlphaDummy088 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_089`. -/
@[expose]
noncomputable def nb067AlphaDummy089 : Var :=
  (freshVar
    (({(nb067AlphaDummy083)} : Finset Var) ∪ ({(nb067AlphaDummy084)} : Finset Var) ∪
      ((synWex (nb067AlphaDummy085) (synWa (synWbr (Class.cv (nb067AlphaDummy083))
              (synCcnv (Class.cv (nb067AlphaDummy000))) (Class.cv (nb067AlphaDummy085)))
            (synWbr (Class.cv (nb067AlphaDummy085)) (Class.cv (nb067AlphaDummy000))
              (Class.cv (nb067AlphaDummy084)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_090`. -/
@[expose]
noncomputable def nb067AlphaDummy090 (f : Var) : Var :=
  (freshVar (({(nb067AlphaDummy086 f)} : Finset Var) ∪
        ({(nb067AlphaDummy087 f)} : Finset Var) ∪ ((synWex (nb067AlphaDummy088 f) (synWa
            (synWbr (Class.cv (nb067AlphaDummy086 f)) (synCcnv (Class.cv f))
              (Class.cv (nb067AlphaDummy088 f)))
            (synWbr (Class.cv (nb067AlphaDummy088 f)) (Class.cv f)
              (Class.cv (nb067AlphaDummy087 f)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_091`. -/
@[expose]
noncomputable def nb067AlphaDummy091 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_092`. -/
@[expose]
noncomputable def nb067AlphaDummy092 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_093`. -/
@[expose]
noncomputable def nb067AlphaDummy093 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy086 f))).fv ∪
      ((Class.cv (nb067AlphaDummy087 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_094`. -/
@[expose]
noncomputable def nb067AlphaDummy094 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy086 f))).fv ∪
      ((Class.cv (nb067AlphaDummy087 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_095`. -/
@[expose]
noncomputable def nb067AlphaDummy095 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCphi (Class.cv (nb067AlphaDummy092)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_096`. -/
@[expose]
noncomputable def nb067AlphaDummy096 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCphi (Class.cv (nb067AlphaDummy094 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_097`. -/
@[expose]
noncomputable def nb067AlphaDummy097 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy091)
          (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
            (Wff.classEq (Class.cv (nb067AlphaDummy091))
              (synCphi (Class.cv (nb067AlphaDummy092))))))).fv ∪
      ((Class.cab (nb067AlphaDummy091)
          (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
            (Wff.classEq (Class.cv (nb067AlphaDummy091))
              (synCphi (Class.cv (nb067AlphaDummy092))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_098`. -/
@[expose]
noncomputable def nb067AlphaDummy098 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy093 f)
          (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
              (synCphi (Class.cv (nb067AlphaDummy094 f))))))).fv ∪
      ((Class.cab (nb067AlphaDummy093 f)
          (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
              (synCphi (Class.cv (nb067AlphaDummy094 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_099`. -/
@[expose]
noncomputable def nb067AlphaDummy099 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy092))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_100`. -/
@[expose]
noncomputable def nb067AlphaDummy100 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy092))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_101`. -/
@[expose]
noncomputable def nb067AlphaDummy101 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy094 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_102`. -/
@[expose]
noncomputable def nb067AlphaDummy102 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy094 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_103`. -/
@[expose]
noncomputable def nb067AlphaDummy103 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy099)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy099)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy099))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_104`. -/
@[expose]
noncomputable def nb067AlphaDummy104 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy101 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy101 f)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy101 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_105`. -/
@[expose]
noncomputable def nb067AlphaDummy105 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_106`. -/
@[expose]
noncomputable def nb067AlphaDummy106 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_107`. -/
@[expose]
noncomputable def nb067AlphaDummy107 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_108`. -/
@[expose]
noncomputable def nb067AlphaDummy108 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_109`. -/
@[expose]
noncomputable def nb067AlphaDummy109 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_110`. -/
@[expose]
noncomputable def nb067AlphaDummy110 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_111`. -/
@[expose]
noncomputable def nb067AlphaDummy111 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy106))
          (Class.cv (nb067AlphaDummy107)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_112`. -/
@[expose]
noncomputable def nb067AlphaDummy112 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy109 f))
          (Class.cv (nb067AlphaDummy110 f)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy109 f)) (Class.cv (nb067AlphaDummy110 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_113`. -/
@[expose]
noncomputable def nb067AlphaDummy113 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_114`. -/
@[expose]
noncomputable def nb067AlphaDummy114 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy109 f))).fv ∪
      ((Class.cv (nb067AlphaDummy110 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_115`. -/
@[expose]
noncomputable def nb067AlphaDummy115 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy106)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy107)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_116`. -/
@[expose]
noncomputable def nb067AlphaDummy116 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy109 f)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy110 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_117`. -/
@[expose]
noncomputable def nb067AlphaDummy117 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy106))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_118`. -/
@[expose]
noncomputable def nb067AlphaDummy118 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy109 f))).fv ∪
      ((Class.cv (nb067AlphaDummy109 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_119`. -/
@[expose]
noncomputable def nb067AlphaDummy119 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy107))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_120`. -/
@[expose]
noncomputable def nb067AlphaDummy120 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy110 f))).fv ∪
      ((Class.cv (nb067AlphaDummy110 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_121`. -/
@[expose]
noncomputable def nb067AlphaDummy121 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy091)
          (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
            (Wff.classEq (Class.cv (nb067AlphaDummy091))
              (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy091)
          (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
            (Wff.classEq (Class.cv (nb067AlphaDummy091))
              (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_122`. -/
@[expose]
noncomputable def nb067AlphaDummy122 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy093 f)
          (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy093 f)
          (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_123`. -/
@[expose]
noncomputable def nb067AlphaDummy123 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy092))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_124`. -/
@[expose]
noncomputable def nb067AlphaDummy124 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy094 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_125`. -/
@[expose]
noncomputable def nb067AlphaDummy125 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy092)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy092)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_126`. -/
@[expose]
noncomputable def nb067AlphaDummy126 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy094 f)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy094 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_127`. -/
@[expose]
noncomputable def nb067AlphaDummy127 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_128`. -/
@[expose]
noncomputable def nb067AlphaDummy128 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_129`. -/
@[expose]
noncomputable def nb067AlphaDummy129 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy086 f))).fv ∪
      ((Class.cv (nb067AlphaDummy088 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_130`. -/
@[expose]
noncomputable def nb067AlphaDummy130 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy086 f))).fv ∪
      ((Class.cv (nb067AlphaDummy088 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_131`. -/
@[expose]
noncomputable def nb067AlphaDummy131 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCphi (Class.cv (nb067AlphaDummy128)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_132`. -/
@[expose]
noncomputable def nb067AlphaDummy132 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCphi (Class.cv (nb067AlphaDummy130 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_133`. -/
@[expose]
noncomputable def nb067AlphaDummy133 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy127)
          (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
            (Wff.classEq (Class.cv (nb067AlphaDummy127))
              (synCphi (Class.cv (nb067AlphaDummy128))))))).fv ∪
      ((Class.cab (nb067AlphaDummy127)
          (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
            (Wff.classEq (Class.cv (nb067AlphaDummy127))
              (synCphi (Class.cv (nb067AlphaDummy128))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_134`. -/
@[expose]
noncomputable def nb067AlphaDummy134 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy129 f)
          (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
              (synCphi (Class.cv (nb067AlphaDummy130 f))))))).fv ∪
      ((Class.cab (nb067AlphaDummy129 f)
          (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
              (synCphi (Class.cv (nb067AlphaDummy130 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_135`. -/
@[expose]
noncomputable def nb067AlphaDummy135 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy128))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_136`. -/
@[expose]
noncomputable def nb067AlphaDummy136 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy128))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_137`. -/
@[expose]
noncomputable def nb067AlphaDummy137 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy130 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_138`. -/
@[expose]
noncomputable def nb067AlphaDummy138 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy130 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_139`. -/
@[expose]
noncomputable def nb067AlphaDummy139 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy135)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy135)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy135))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_140`. -/
@[expose]
noncomputable def nb067AlphaDummy140 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy137 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy137 f)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy137 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_141`. -/
@[expose]
noncomputable def nb067AlphaDummy141 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_142`. -/
@[expose]
noncomputable def nb067AlphaDummy142 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_143`. -/
@[expose]
noncomputable def nb067AlphaDummy143 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_144`. -/
@[expose]
noncomputable def nb067AlphaDummy144 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_145`. -/
@[expose]
noncomputable def nb067AlphaDummy145 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_146`. -/
@[expose]
noncomputable def nb067AlphaDummy146 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_147`. -/
@[expose]
noncomputable def nb067AlphaDummy147 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy142))
          (Class.cv (nb067AlphaDummy143)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_148`. -/
@[expose]
noncomputable def nb067AlphaDummy148 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy145 f))
          (Class.cv (nb067AlphaDummy146 f)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy145 f)) (Class.cv (nb067AlphaDummy146 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_149`. -/
@[expose]
noncomputable def nb067AlphaDummy149 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_150`. -/
@[expose]
noncomputable def nb067AlphaDummy150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy145 f))).fv ∪
      ((Class.cv (nb067AlphaDummy146 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_151`. -/
@[expose]
noncomputable def nb067AlphaDummy151 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy142)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy143)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_152`. -/
@[expose]
noncomputable def nb067AlphaDummy152 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy145 f)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy146 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_153`. -/
@[expose]
noncomputable def nb067AlphaDummy153 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy142))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_154`. -/
@[expose]
noncomputable def nb067AlphaDummy154 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy145 f))).fv ∪
      ((Class.cv (nb067AlphaDummy145 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_155`. -/
@[expose]
noncomputable def nb067AlphaDummy155 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy143))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_156`. -/
@[expose]
noncomputable def nb067AlphaDummy156 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy146 f))).fv ∪
      ((Class.cv (nb067AlphaDummy146 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_157`. -/
@[expose]
noncomputable def nb067AlphaDummy157 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy127)
          (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
            (Wff.classEq (Class.cv (nb067AlphaDummy127))
              (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy127)
          (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
            (Wff.classEq (Class.cv (nb067AlphaDummy127))
              (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_158`. -/
@[expose]
noncomputable def nb067AlphaDummy158 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy129 f)
          (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy129 f)
          (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_159`. -/
@[expose]
noncomputable def nb067AlphaDummy159 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy128))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_160`. -/
@[expose]
noncomputable def nb067AlphaDummy160 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy130 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_161`. -/
@[expose]
noncomputable def nb067AlphaDummy161 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy128)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy128)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_162`. -/
@[expose]
noncomputable def nb067AlphaDummy162 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy130 f)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy130 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_163`. -/
@[expose]
noncomputable def nb067AlphaDummy163 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_164`. -/
@[expose]
noncomputable def nb067AlphaDummy164 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_165`. -/
@[expose]
noncomputable def nb067AlphaDummy165 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_166`. -/
@[expose]
noncomputable def nb067AlphaDummy166 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_167`. -/
@[expose]
noncomputable def nb067AlphaDummy167 : Var :=
  (freshVar
    (({(nb067AlphaDummy163)} : Finset Var) ∪ ({(nb067AlphaDummy164)} : Finset Var) ∪
      ((synWbr (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy000))
          (Class.cv (nb067AlphaDummy163)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_168`. -/
@[expose]
noncomputable def nb067AlphaDummy168 (f : Var) : Var :=
  (freshVar (({(nb067AlphaDummy165 f)} : Finset Var) ∪
        ({(nb067AlphaDummy166 f)} : Finset Var) ∪
      ((synWbr (Class.cv (nb067AlphaDummy166 f)) (Class.cv f)
          (Class.cv (nb067AlphaDummy165 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_169`. -/
@[expose]
noncomputable def nb067AlphaDummy169 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_170`. -/
@[expose]
noncomputable def nb067AlphaDummy170 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_171`. -/
@[expose]
noncomputable def nb067AlphaDummy171 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy165 f))).fv ∪
      ((Class.cv (nb067AlphaDummy166 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_172`. -/
@[expose]
noncomputable def nb067AlphaDummy172 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy165 f))).fv ∪
      ((Class.cv (nb067AlphaDummy166 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_173`. -/
@[expose]
noncomputable def nb067AlphaDummy173 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCphi (Class.cv (nb067AlphaDummy170)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_174`. -/
@[expose]
noncomputable def nb067AlphaDummy174 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCphi (Class.cv (nb067AlphaDummy172 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_175`. -/
@[expose]
noncomputable def nb067AlphaDummy175 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy169)
          (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
            (Wff.classEq (Class.cv (nb067AlphaDummy169))
              (synCphi (Class.cv (nb067AlphaDummy170))))))).fv ∪
      ((Class.cab (nb067AlphaDummy169)
          (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
            (Wff.classEq (Class.cv (nb067AlphaDummy169))
              (synCphi (Class.cv (nb067AlphaDummy170))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_176`. -/
@[expose]
noncomputable def nb067AlphaDummy176 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy171 f)
          (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
              (synCphi (Class.cv (nb067AlphaDummy172 f))))))).fv ∪
      ((Class.cab (nb067AlphaDummy171 f)
          (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
              (synCphi (Class.cv (nb067AlphaDummy172 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_177`. -/
@[expose]
noncomputable def nb067AlphaDummy177 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy170))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_178`. -/
@[expose]
noncomputable def nb067AlphaDummy178 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy170))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_179`. -/
@[expose]
noncomputable def nb067AlphaDummy179 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy172 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_180`. -/
@[expose]
noncomputable def nb067AlphaDummy180 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy172 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_181`. -/
@[expose]
noncomputable def nb067AlphaDummy181 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy177))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_182`. -/
@[expose]
noncomputable def nb067AlphaDummy182 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy179 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_183`. -/
@[expose]
noncomputable def nb067AlphaDummy183 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_184`. -/
@[expose]
noncomputable def nb067AlphaDummy184 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_185`. -/
@[expose]
noncomputable def nb067AlphaDummy185 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_186`. -/
@[expose]
noncomputable def nb067AlphaDummy186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_187`. -/
@[expose]
noncomputable def nb067AlphaDummy187 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_188`. -/
@[expose]
noncomputable def nb067AlphaDummy188 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_189`. -/
@[expose]
noncomputable def nb067AlphaDummy189 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy184))
          (Class.cv (nb067AlphaDummy185)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_190`. -/
@[expose]
noncomputable def nb067AlphaDummy190 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy187 f))
          (Class.cv (nb067AlphaDummy188 f)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy187 f)) (Class.cv (nb067AlphaDummy188 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_191`. -/
@[expose]
noncomputable def nb067AlphaDummy191 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_192`. -/
@[expose]
noncomputable def nb067AlphaDummy192 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy187 f))).fv ∪
      ((Class.cv (nb067AlphaDummy188 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_193`. -/
@[expose]
noncomputable def nb067AlphaDummy193 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy184)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy185)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_194`. -/
@[expose]
noncomputable def nb067AlphaDummy194 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy187 f)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy188 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_195`. -/
@[expose]
noncomputable def nb067AlphaDummy195 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy184))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_196`. -/
@[expose]
noncomputable def nb067AlphaDummy196 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy187 f))).fv ∪
      ((Class.cv (nb067AlphaDummy187 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_197`. -/
@[expose]
noncomputable def nb067AlphaDummy197 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy185))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_198`. -/
@[expose]
noncomputable def nb067AlphaDummy198 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy188 f))).fv ∪
      ((Class.cv (nb067AlphaDummy188 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_199`. -/
@[expose]
noncomputable def nb067AlphaDummy199 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy169)
          (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
            (Wff.classEq (Class.cv (nb067AlphaDummy169))
              (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy169)
          (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
            (Wff.classEq (Class.cv (nb067AlphaDummy169))
              (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_200`. -/
@[expose]
noncomputable def nb067AlphaDummy200 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy171 f)
          (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy171 f)
          (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_201`. -/
@[expose]
noncomputable def nb067AlphaDummy201 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy170))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_202`. -/
@[expose]
noncomputable def nb067AlphaDummy202 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy172 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_203`. -/
@[expose]
noncomputable def nb067AlphaDummy203 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy170)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy170)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_204`. -/
@[expose]
noncomputable def nb067AlphaDummy204 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy172 f)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy172 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_205`. -/
@[expose]
noncomputable def nb067AlphaDummy205 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_206`. -/
@[expose]
noncomputable def nb067AlphaDummy206 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_207`. -/
@[expose]
noncomputable def nb067AlphaDummy207 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy166 f))).fv ∪
      ((Class.cv (nb067AlphaDummy165 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_208`. -/
@[expose]
noncomputable def nb067AlphaDummy208 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy166 f))).fv ∪
      ((Class.cv (nb067AlphaDummy165 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_209`. -/
@[expose]
noncomputable def nb067AlphaDummy209 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCphi (Class.cv (nb067AlphaDummy206)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_210`. -/
@[expose]
noncomputable def nb067AlphaDummy210 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCphi (Class.cv (nb067AlphaDummy208 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_211`. -/
@[expose]
noncomputable def nb067AlphaDummy211 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy205)
          (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
            (Wff.classEq (Class.cv (nb067AlphaDummy205))
              (synCphi (Class.cv (nb067AlphaDummy206))))))).fv ∪
      ((Class.cab (nb067AlphaDummy205)
          (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
            (Wff.classEq (Class.cv (nb067AlphaDummy205))
              (synCphi (Class.cv (nb067AlphaDummy206))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_212`. -/
@[expose]
noncomputable def nb067AlphaDummy212 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy207 f)
          (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
              (synCphi (Class.cv (nb067AlphaDummy208 f))))))).fv ∪
      ((Class.cab (nb067AlphaDummy207 f)
          (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
              (synCphi (Class.cv (nb067AlphaDummy208 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_213`. -/
@[expose]
noncomputable def nb067AlphaDummy213 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy206))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_214`. -/
@[expose]
noncomputable def nb067AlphaDummy214 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy206))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_215`. -/
@[expose]
noncomputable def nb067AlphaDummy215 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy208 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_216`. -/
@[expose]
noncomputable def nb067AlphaDummy216 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy208 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_217`. -/
@[expose]
noncomputable def nb067AlphaDummy217 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy213))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_218`. -/
@[expose]
noncomputable def nb067AlphaDummy218 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy215 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_219`. -/
@[expose]
noncomputable def nb067AlphaDummy219 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_220`. -/
@[expose]
noncomputable def nb067AlphaDummy220 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_221`. -/
@[expose]
noncomputable def nb067AlphaDummy221 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_222`. -/
@[expose]
noncomputable def nb067AlphaDummy222 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_223`. -/
@[expose]
noncomputable def nb067AlphaDummy223 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_224`. -/
@[expose]
noncomputable def nb067AlphaDummy224 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_225`. -/
@[expose]
noncomputable def nb067AlphaDummy225 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy220))
          (Class.cv (nb067AlphaDummy221)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_226`. -/
@[expose]
noncomputable def nb067AlphaDummy226 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy223 f))
          (Class.cv (nb067AlphaDummy224 f)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy223 f)) (Class.cv (nb067AlphaDummy224 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_227`. -/
@[expose]
noncomputable def nb067AlphaDummy227 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_228`. -/
@[expose]
noncomputable def nb067AlphaDummy228 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy223 f))).fv ∪
      ((Class.cv (nb067AlphaDummy224 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_229`. -/
@[expose]
noncomputable def nb067AlphaDummy229 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy220)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy221)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_230`. -/
@[expose]
noncomputable def nb067AlphaDummy230 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy223 f)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy224 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_231`. -/
@[expose]
noncomputable def nb067AlphaDummy231 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy220))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_232`. -/
@[expose]
noncomputable def nb067AlphaDummy232 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy223 f))).fv ∪
      ((Class.cv (nb067AlphaDummy223 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_233`. -/
@[expose]
noncomputable def nb067AlphaDummy233 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy221))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_234`. -/
@[expose]
noncomputable def nb067AlphaDummy234 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy224 f))).fv ∪
      ((Class.cv (nb067AlphaDummy224 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_235`. -/
@[expose]
noncomputable def nb067AlphaDummy235 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy205)
          (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
            (Wff.classEq (Class.cv (nb067AlphaDummy205))
              (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy205)
          (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
            (Wff.classEq (Class.cv (nb067AlphaDummy205))
              (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_236`. -/
@[expose]
noncomputable def nb067AlphaDummy236 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy207 f)
          (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy207 f)
          (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_237`. -/
@[expose]
noncomputable def nb067AlphaDummy237 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy206))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_238`. -/
@[expose]
noncomputable def nb067AlphaDummy238 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy208 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_239`. -/
@[expose]
noncomputable def nb067AlphaDummy239 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy206)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy206)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_240`. -/
@[expose]
noncomputable def nb067AlphaDummy240 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy208 f)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy208 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_241`. -/
@[expose]
noncomputable def nb067AlphaDummy241 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_242`. -/
@[expose]
noncomputable def nb067AlphaDummy242 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_243`. -/
@[expose]
noncomputable def nb067AlphaDummy243 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy088 f))).fv ∪
      ((Class.cv (nb067AlphaDummy087 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_244`. -/
@[expose]
noncomputable def nb067AlphaDummy244 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy088 f))).fv ∪
      ((Class.cv (nb067AlphaDummy087 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_245`. -/
@[expose]
noncomputable def nb067AlphaDummy245 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCphi (Class.cv (nb067AlphaDummy242)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_246`. -/
@[expose]
noncomputable def nb067AlphaDummy246 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCphi (Class.cv (nb067AlphaDummy244 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_247`. -/
@[expose]
noncomputable def nb067AlphaDummy247 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy241)
          (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
            (Wff.classEq (Class.cv (nb067AlphaDummy241))
              (synCphi (Class.cv (nb067AlphaDummy242))))))).fv ∪
      ((Class.cab (nb067AlphaDummy241)
          (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
            (Wff.classEq (Class.cv (nb067AlphaDummy241))
              (synCphi (Class.cv (nb067AlphaDummy242))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_248`. -/
@[expose]
noncomputable def nb067AlphaDummy248 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy243 f)
          (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
              (synCphi (Class.cv (nb067AlphaDummy244 f))))))).fv ∪
      ((Class.cab (nb067AlphaDummy243 f)
          (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
              (synCphi (Class.cv (nb067AlphaDummy244 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_249`. -/
@[expose]
noncomputable def nb067AlphaDummy249 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy242))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_250`. -/
@[expose]
noncomputable def nb067AlphaDummy250 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy242))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_251`. -/
@[expose]
noncomputable def nb067AlphaDummy251 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy244 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_252`. -/
@[expose]
noncomputable def nb067AlphaDummy252 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy244 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_253`. -/
@[expose]
noncomputable def nb067AlphaDummy253 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy249)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy249)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy249))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_254`. -/
@[expose]
noncomputable def nb067AlphaDummy254 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy251 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy251 f)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy251 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_255`. -/
@[expose]
noncomputable def nb067AlphaDummy255 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_256`. -/
@[expose]
noncomputable def nb067AlphaDummy256 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_257`. -/
@[expose]
noncomputable def nb067AlphaDummy257 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_258`. -/
@[expose]
noncomputable def nb067AlphaDummy258 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_259`. -/
@[expose]
noncomputable def nb067AlphaDummy259 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_260`. -/
@[expose]
noncomputable def nb067AlphaDummy260 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_261`. -/
@[expose]
noncomputable def nb067AlphaDummy261 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy256))
          (Class.cv (nb067AlphaDummy257)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_262`. -/
@[expose]
noncomputable def nb067AlphaDummy262 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy259 f))
          (Class.cv (nb067AlphaDummy260 f)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy259 f)) (Class.cv (nb067AlphaDummy260 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_263`. -/
@[expose]
noncomputable def nb067AlphaDummy263 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_264`. -/
@[expose]
noncomputable def nb067AlphaDummy264 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy259 f))).fv ∪
      ((Class.cv (nb067AlphaDummy260 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_265`. -/
@[expose]
noncomputable def nb067AlphaDummy265 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy256)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy257)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_266`. -/
@[expose]
noncomputable def nb067AlphaDummy266 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy259 f)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy260 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_267`. -/
@[expose]
noncomputable def nb067AlphaDummy267 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy256))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_268`. -/
@[expose]
noncomputable def nb067AlphaDummy268 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy259 f))).fv ∪
      ((Class.cv (nb067AlphaDummy259 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_269`. -/
@[expose]
noncomputable def nb067AlphaDummy269 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy257))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_270`. -/
@[expose]
noncomputable def nb067AlphaDummy270 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy260 f))).fv ∪
      ((Class.cv (nb067AlphaDummy260 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_271`. -/
@[expose]
noncomputable def nb067AlphaDummy271 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy241)
          (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
            (Wff.classEq (Class.cv (nb067AlphaDummy241))
              (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy241)
          (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
            (Wff.classEq (Class.cv (nb067AlphaDummy241))
              (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_272`. -/
@[expose]
noncomputable def nb067AlphaDummy272 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy243 f)
          (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy243 f)
          (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_273`. -/
@[expose]
noncomputable def nb067AlphaDummy273 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy242))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_274`. -/
@[expose]
noncomputable def nb067AlphaDummy274 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy244 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_275`. -/
@[expose]
noncomputable def nb067AlphaDummy275 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy242)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy242)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_276`. -/
@[expose]
noncomputable def nb067AlphaDummy276 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy244 f)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy244 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_277`. -/
@[expose]
noncomputable def nb067AlphaDummy277 : Var :=
  (freshVar (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_278`. -/
@[expose]
noncomputable def nb067AlphaDummy278 : Var :=
  (freshVar (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_279`. -/
@[expose]
noncomputable def nb067AlphaDummy279 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_280`. -/
@[expose]
noncomputable def nb067AlphaDummy280 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_281`. -/
@[expose]
noncomputable def nb067AlphaDummy281 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_282`. -/
@[expose]
noncomputable def nb067AlphaDummy282 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_283`. -/
@[expose]
noncomputable def nb067AlphaDummy283 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy280 f))).fv ∪
      ((Class.cv (nb067AlphaDummy279 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_284`. -/
@[expose]
noncomputable def nb067AlphaDummy284 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy280 f))).fv ∪
      ((Class.cv (nb067AlphaDummy279 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_285`. -/
@[expose]
noncomputable def nb067AlphaDummy285 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCphi (Class.cv (nb067AlphaDummy282)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_286`. -/
@[expose]
noncomputable def nb067AlphaDummy286 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCphi (Class.cv (nb067AlphaDummy284 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_287`. -/
@[expose]
noncomputable def nb067AlphaDummy287 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy281)
          (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
            (Wff.classEq (Class.cv (nb067AlphaDummy281))
              (synCphi (Class.cv (nb067AlphaDummy282))))))).fv ∪
      ((Class.cab (nb067AlphaDummy281)
          (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
            (Wff.classEq (Class.cv (nb067AlphaDummy281))
              (synCphi (Class.cv (nb067AlphaDummy282))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_288`. -/
@[expose]
noncomputable def nb067AlphaDummy288 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy283 f)
          (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
              (synCphi (Class.cv (nb067AlphaDummy284 f))))))).fv ∪
      ((Class.cab (nb067AlphaDummy283 f)
          (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
              (synCphi (Class.cv (nb067AlphaDummy284 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_289`. -/
@[expose]
noncomputable def nb067AlphaDummy289 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy282))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_290`. -/
@[expose]
noncomputable def nb067AlphaDummy290 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy282))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_291`. -/
@[expose]
noncomputable def nb067AlphaDummy291 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy284 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_292`. -/
@[expose]
noncomputable def nb067AlphaDummy292 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy284 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_293`. -/
@[expose]
noncomputable def nb067AlphaDummy293 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy289)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy289)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy289))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_294`. -/
@[expose]
noncomputable def nb067AlphaDummy294 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy291 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy291 f)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy291 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_295`. -/
@[expose]
noncomputable def nb067AlphaDummy295 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_296`. -/
@[expose]
noncomputable def nb067AlphaDummy296 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_297`. -/
@[expose]
noncomputable def nb067AlphaDummy297 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_298`. -/
@[expose]
noncomputable def nb067AlphaDummy298 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_299`. -/
@[expose]
noncomputable def nb067AlphaDummy299 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_300`. -/
@[expose]
noncomputable def nb067AlphaDummy300 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_301`. -/
@[expose]
noncomputable def nb067AlphaDummy301 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy296))
          (Class.cv (nb067AlphaDummy297)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_302`. -/
@[expose]
noncomputable def nb067AlphaDummy302 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy299 f))
          (Class.cv (nb067AlphaDummy300 f)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy299 f)) (Class.cv (nb067AlphaDummy300 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_303`. -/
@[expose]
noncomputable def nb067AlphaDummy303 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_304`. -/
@[expose]
noncomputable def nb067AlphaDummy304 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy299 f))).fv ∪
      ((Class.cv (nb067AlphaDummy300 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_305`. -/
@[expose]
noncomputable def nb067AlphaDummy305 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy296)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy297)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_306`. -/
@[expose]
noncomputable def nb067AlphaDummy306 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy299 f)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy300 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_307`. -/
@[expose]
noncomputable def nb067AlphaDummy307 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy296))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_308`. -/
@[expose]
noncomputable def nb067AlphaDummy308 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy299 f))).fv ∪
      ((Class.cv (nb067AlphaDummy299 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_309`. -/
@[expose]
noncomputable def nb067AlphaDummy309 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy297))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_310`. -/
@[expose]
noncomputable def nb067AlphaDummy310 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy300 f))).fv ∪
      ((Class.cv (nb067AlphaDummy300 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_311`. -/
@[expose]
noncomputable def nb067AlphaDummy311 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy281)
          (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
            (Wff.classEq (Class.cv (nb067AlphaDummy281))
              (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy281)
          (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
            (Wff.classEq (Class.cv (nb067AlphaDummy281))
              (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_312`. -/
@[expose]
noncomputable def nb067AlphaDummy312 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy283 f)
          (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy283 f)
          (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_313`. -/
@[expose]
noncomputable def nb067AlphaDummy313 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy282))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_314`. -/
@[expose]
noncomputable def nb067AlphaDummy314 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy284 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_315`. -/
@[expose]
noncomputable def nb067AlphaDummy315 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy282)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy282)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_316`. -/
@[expose]
noncomputable def nb067AlphaDummy316 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy284 f)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy284 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_317`. -/
@[expose]
noncomputable def nb067AlphaDummy317 : Var :=
  (freshVar (((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
          (Class.cv (nb067AlphaDummy001)))).fv ∪
      ((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
          (Class.cv (nb067AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_318`. -/
@[expose]
noncomputable def nb067AlphaDummy318 (x : Var) (f : Var) : Var :=
  (freshVar (((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv ∪
      ((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_319`. -/
@[expose]
noncomputable def nb067AlphaDummy319 : Var :=
  (freshVar (((synCrn (Class.cv (nb067AlphaDummy000)))).fv ∪
      ((Class.cv (nb067AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_320`. -/
@[expose]
noncomputable def nb067AlphaDummy320 (x : Var) (f : Var) : Var :=
  (freshVar (((synCrn (Class.cv f))).fv ∪ ((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_321`. -/
@[expose]
noncomputable def nb067AlphaDummy321 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_322`. -/
@[expose]
noncomputable def nb067AlphaDummy322 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_323`. -/
@[expose]
noncomputable def nb067AlphaDummy323 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_324`. -/
@[expose]
noncomputable def nb067AlphaDummy324 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_325`. -/
@[expose]
noncomputable def nb067AlphaDummy325 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_326`. -/
@[expose]
noncomputable def nb067AlphaDummy326 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_327`. -/
@[expose]
noncomputable def nb067AlphaDummy327 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy324 f))).fv ∪
      ((Class.cv (nb067AlphaDummy323 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_328`. -/
@[expose]
noncomputable def nb067AlphaDummy328 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy324 f))).fv ∪
      ((Class.cv (nb067AlphaDummy323 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_329`. -/
@[expose]
noncomputable def nb067AlphaDummy329 : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCphi (Class.cv (nb067AlphaDummy326)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_330`. -/
@[expose]
noncomputable def nb067AlphaDummy330 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCphi (Class.cv (nb067AlphaDummy328 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_331`. -/
@[expose]
noncomputable def nb067AlphaDummy331 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy325)
          (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
            (Wff.classEq (Class.cv (nb067AlphaDummy325))
              (synCphi (Class.cv (nb067AlphaDummy326))))))).fv ∪
      ((Class.cab (nb067AlphaDummy325)
          (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
            (Wff.classEq (Class.cv (nb067AlphaDummy325))
              (synCphi (Class.cv (nb067AlphaDummy326))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_332`. -/
@[expose]
noncomputable def nb067AlphaDummy332 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy327 f)
          (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
              (synCphi (Class.cv (nb067AlphaDummy328 f))))))).fv ∪
      ((Class.cab (nb067AlphaDummy327 f)
          (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
              (synCphi (Class.cv (nb067AlphaDummy328 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_333`. -/
@[expose]
noncomputable def nb067AlphaDummy333 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy326))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_334`. -/
@[expose]
noncomputable def nb067AlphaDummy334 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy326))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_335`. -/
@[expose]
noncomputable def nb067AlphaDummy335 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy328 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_336`. -/
@[expose]
noncomputable def nb067AlphaDummy336 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy328 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_337`. -/
@[expose]
noncomputable def nb067AlphaDummy337 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy333)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy333)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy333))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_338`. -/
@[expose]
noncomputable def nb067AlphaDummy338 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb067AlphaDummy335 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb067AlphaDummy335 f)) (synC1c))).fv ∪
      ((Class.cv (nb067AlphaDummy335 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_339`. -/
@[expose]
noncomputable def nb067AlphaDummy339 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_340`. -/
@[expose]
noncomputable def nb067AlphaDummy340 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_341`. -/
@[expose]
noncomputable def nb067AlphaDummy341 : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_342`. -/
@[expose]
noncomputable def nb067AlphaDummy342 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_343`. -/
@[expose]
noncomputable def nb067AlphaDummy343 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_344`. -/
@[expose]
noncomputable def nb067AlphaDummy344 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_345`. -/
@[expose]
noncomputable def nb067AlphaDummy345 : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy340))
          (Class.cv (nb067AlphaDummy341)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_346`. -/
@[expose]
noncomputable def nb067AlphaDummy346 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb067AlphaDummy343 f))
          (Class.cv (nb067AlphaDummy344 f)))).fv ∪
      ((synCnin (Class.cv (nb067AlphaDummy343 f)) (Class.cv (nb067AlphaDummy344 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_347`. -/
@[expose]
noncomputable def nb067AlphaDummy347 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_348`. -/
@[expose]
noncomputable def nb067AlphaDummy348 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy343 f))).fv ∪
      ((Class.cv (nb067AlphaDummy344 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_349`. -/
@[expose]
noncomputable def nb067AlphaDummy349 : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy340)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy341)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_350`. -/
@[expose]
noncomputable def nb067AlphaDummy350 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb067AlphaDummy343 f)))).fv ∪
      ((synCcompl (Class.cv (nb067AlphaDummy344 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_351`. -/
@[expose]
noncomputable def nb067AlphaDummy351 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy340))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_352`. -/
@[expose]
noncomputable def nb067AlphaDummy352 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy343 f))).fv ∪
      ((Class.cv (nb067AlphaDummy343 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_353`. -/
@[expose]
noncomputable def nb067AlphaDummy353 : Var :=
  (freshVar
    (((Class.cv (nb067AlphaDummy341))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_354`. -/
@[expose]
noncomputable def nb067AlphaDummy354 (f : Var) : Var :=
  (freshVar (((Class.cv (nb067AlphaDummy344 f))).fv ∪
      ((Class.cv (nb067AlphaDummy344 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_355`. -/
@[expose]
noncomputable def nb067AlphaDummy355 : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy325)
          (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
            (Wff.classEq (Class.cv (nb067AlphaDummy325))
              (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy325)
          (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
            (Wff.classEq (Class.cv (nb067AlphaDummy325))
              (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_356`. -/
@[expose]
noncomputable def nb067AlphaDummy356 (f : Var) : Var :=
  (freshVar (((Class.cab (nb067AlphaDummy327 f)
          (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy327 f)
          (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
            (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
              (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_357`. -/
@[expose]
noncomputable def nb067AlphaDummy357 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy326))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_358`. -/
@[expose]
noncomputable def nb067AlphaDummy358 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb067AlphaDummy328 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_359`. -/
@[expose]
noncomputable def nb067AlphaDummy359 : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy326)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy326)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb067_alpha_dummy_360`. -/
@[expose]
noncomputable def nb067AlphaDummy360 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb067AlphaDummy328 f)))).fv ∪
      ((synCphi (Class.cv (nb067AlphaDummy328 f)))).fv) 0)

theorem nb067_fresh_000 :
    (nb067AlphaDummy073) ∉
      (((Class.cab (nb067AlphaDummy007)
            (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy007)
            (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy007)
            (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy007)
            (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_001 :
    (nb067AlphaDummy013) ∉
      (((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008))))))).fv ∪
        ((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008))))))).fv) :=
  by
  simpa only [nb067AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008))))))).fv ∪
        ((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008))))))).fv)
      0

theorem nb067_fresh_002 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy074 x y f) ∉
      (((Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
              (Class.cv (nb067AlphaDummy004 x y f))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (Class.cv (nb067AlphaDummy004 x y f))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy074] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
              (Class.cv (nb067AlphaDummy004 x y f))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (Class.cv (nb067AlphaDummy004 x y f))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_003 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy014 x y f) ∉
      (((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv) :=
  by
  simpa only [nb067AlphaDummy014] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv)
      0

theorem nb067_fresh_004 :
    (nb067AlphaDummy021) ∉
      (((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCphi (Class.cv (nb067AlphaDummy016))))))).fv ∪
        ((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCphi (Class.cv (nb067AlphaDummy016))))))).fv) :=
  by
  simpa only [nb067AlphaDummy021] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCphi (Class.cv (nb067AlphaDummy016))))))).fv ∪
        ((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCphi (Class.cv (nb067AlphaDummy016))))))).fv)
      0

theorem nb067_fresh_005 :
    (nb067AlphaDummy045) ∉
      (((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy045] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_006 (x : Var) (y : Var) :
    (nb067AlphaDummy022 x y) ∉
      (((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCphi (Class.cv (nb067AlphaDummy018 x y))))))).fv ∪
        ((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCphi (Class.cv (nb067AlphaDummy018 x y))))))).fv) :=
  by
  simpa only [nb067AlphaDummy022] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCphi (Class.cv (nb067AlphaDummy018 x y))))))).fv ∪
        ((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCphi (Class.cv (nb067AlphaDummy018 x y))))))).fv)
      0

theorem nb067_fresh_007 (x : Var) (y : Var) :
    (nb067AlphaDummy046 x y) ∉
      (((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy046] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_008 :
    (nb067AlphaDummy097) ∉
      (((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCphi (Class.cv (nb067AlphaDummy092))))))).fv ∪
        ((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCphi (Class.cv (nb067AlphaDummy092))))))).fv) :=
  by
  simpa only [nb067AlphaDummy097] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCphi (Class.cv (nb067AlphaDummy092))))))).fv ∪
        ((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCphi (Class.cv (nb067AlphaDummy092))))))).fv)
      0

theorem nb067_fresh_009 :
    (nb067AlphaDummy121) ∉
      (((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy121] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_010 (f : Var) :
    (nb067AlphaDummy098 f) ∉
      (((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCphi (Class.cv (nb067AlphaDummy094 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCphi (Class.cv (nb067AlphaDummy094 f))))))).fv) :=
  by
  simpa only [nb067AlphaDummy098] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCphi (Class.cv (nb067AlphaDummy094 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCphi (Class.cv (nb067AlphaDummy094 f))))))).fv)
      0

theorem nb067_fresh_011 (f : Var) :
    (nb067AlphaDummy122 f) ∉
      (((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy122] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_012 :
    (nb067AlphaDummy133) ∉
      (((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCphi (Class.cv (nb067AlphaDummy128))))))).fv ∪
        ((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCphi (Class.cv (nb067AlphaDummy128))))))).fv) :=
  by
  simpa only [nb067AlphaDummy133] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCphi (Class.cv (nb067AlphaDummy128))))))).fv ∪
        ((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCphi (Class.cv (nb067AlphaDummy128))))))).fv)
      0

theorem nb067_fresh_013 :
    (nb067AlphaDummy157) ∉
      (((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy157] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_014 (f : Var) :
    (nb067AlphaDummy134 f) ∉
      (((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCphi (Class.cv (nb067AlphaDummy130 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCphi (Class.cv (nb067AlphaDummy130 f))))))).fv) :=
  by
  simpa only [nb067AlphaDummy134] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCphi (Class.cv (nb067AlphaDummy130 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCphi (Class.cv (nb067AlphaDummy130 f))))))).fv)
      0

theorem nb067_fresh_015 (f : Var) :
    (nb067AlphaDummy158 f) ∉
      (((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy158] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_016 :
    (nb067AlphaDummy175) ∉
      (((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCphi (Class.cv (nb067AlphaDummy170))))))).fv ∪
        ((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCphi (Class.cv (nb067AlphaDummy170))))))).fv) :=
  by
  simpa only [nb067AlphaDummy175] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCphi (Class.cv (nb067AlphaDummy170))))))).fv ∪
        ((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCphi (Class.cv (nb067AlphaDummy170))))))).fv)
      0

theorem nb067_fresh_017 :
    (nb067AlphaDummy199) ∉
      (((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy199] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_018 (f : Var) :
    (nb067AlphaDummy176 f) ∉
      (((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCphi (Class.cv (nb067AlphaDummy172 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCphi (Class.cv (nb067AlphaDummy172 f))))))).fv) :=
  by
  simpa only [nb067AlphaDummy176] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCphi (Class.cv (nb067AlphaDummy172 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCphi (Class.cv (nb067AlphaDummy172 f))))))).fv)
      0

theorem nb067_fresh_019 (f : Var) :
    (nb067AlphaDummy200 f) ∉
      (((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy200] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_020 :
    (nb067AlphaDummy235) ∉
      (((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy235] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_021 :
    (nb067AlphaDummy211) ∉
      (((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCphi (Class.cv (nb067AlphaDummy206))))))).fv ∪
        ((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCphi (Class.cv (nb067AlphaDummy206))))))).fv) :=
  by
  simpa only [nb067AlphaDummy211] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCphi (Class.cv (nb067AlphaDummy206))))))).fv ∪
        ((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCphi (Class.cv (nb067AlphaDummy206))))))).fv)
      0

theorem nb067_fresh_022 (f : Var) :
    (nb067AlphaDummy236 f) ∉
      (((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy236] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_023 (f : Var) :
    (nb067AlphaDummy212 f) ∉
      (((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCphi (Class.cv (nb067AlphaDummy208 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCphi (Class.cv (nb067AlphaDummy208 f))))))).fv) :=
  by
  simpa only [nb067AlphaDummy212] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCphi (Class.cv (nb067AlphaDummy208 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCphi (Class.cv (nb067AlphaDummy208 f))))))).fv)
      0

theorem nb067_fresh_024 :
    (nb067AlphaDummy271) ∉
      (((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy271] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_025 :
    (nb067AlphaDummy247) ∉
      (((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCphi (Class.cv (nb067AlphaDummy242))))))).fv ∪
        ((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCphi (Class.cv (nb067AlphaDummy242))))))).fv) :=
  by
  simpa only [nb067AlphaDummy247] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCphi (Class.cv (nb067AlphaDummy242))))))).fv ∪
        ((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCphi (Class.cv (nb067AlphaDummy242))))))).fv)
      0

theorem nb067_fresh_026 (f : Var) :
    (nb067AlphaDummy272 f) ∉
      (((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy272] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_027 (f : Var) :
    (nb067AlphaDummy248 f) ∉
      (((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCphi (Class.cv (nb067AlphaDummy244 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCphi (Class.cv (nb067AlphaDummy244 f))))))).fv) :=
  by
  simpa only [nb067AlphaDummy248] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCphi (Class.cv (nb067AlphaDummy244 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCphi (Class.cv (nb067AlphaDummy244 f))))))).fv)
      0

theorem nb067_fresh_028 :
    (nb067AlphaDummy311) ∉
      (((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy311] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_029 :
    (nb067AlphaDummy287) ∉
      (((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCphi (Class.cv (nb067AlphaDummy282))))))).fv ∪
        ((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCphi (Class.cv (nb067AlphaDummy282))))))).fv) :=
  by
  simpa only [nb067AlphaDummy287] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCphi (Class.cv (nb067AlphaDummy282))))))).fv ∪
        ((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCphi (Class.cv (nb067AlphaDummy282))))))).fv)
      0

theorem nb067_fresh_030 (f : Var) :
    (nb067AlphaDummy312 f) ∉
      (((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy312] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_031 (f : Var) :
    (nb067AlphaDummy288 f) ∉
      (((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCphi (Class.cv (nb067AlphaDummy284 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCphi (Class.cv (nb067AlphaDummy284 f))))))).fv) :=
  by
  simpa only [nb067AlphaDummy288] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCphi (Class.cv (nb067AlphaDummy284 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCphi (Class.cv (nb067AlphaDummy284 f))))))).fv)
      0

theorem nb067_fresh_032 :
    (nb067AlphaDummy355) ∉
      (((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy355] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_033 :
    (nb067AlphaDummy331) ∉
      (((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCphi (Class.cv (nb067AlphaDummy326))))))).fv ∪
        ((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCphi (Class.cv (nb067AlphaDummy326))))))).fv) :=
  by
  simpa only [nb067AlphaDummy331] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCphi (Class.cv (nb067AlphaDummy326))))))).fv ∪
        ((Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCphi (Class.cv (nb067AlphaDummy326))))))).fv)
      0

theorem nb067_fresh_034 (f : Var) :
    (nb067AlphaDummy356 f) ∉
      (((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb067AlphaDummy356] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb067_fresh_035 (f : Var) :
    (nb067AlphaDummy332 f) ∉
      (((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCphi (Class.cv (nb067AlphaDummy328 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCphi (Class.cv (nb067AlphaDummy328 f))))))).fv) :=
  by
  simpa only [nb067AlphaDummy332] using
    freshVar_not_mem
      (((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCphi (Class.cv (nb067AlphaDummy328 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCphi (Class.cv (nb067AlphaDummy328 f))))))).fv)
      0

theorem nb067_fresh_036 :
    (nb067AlphaDummy163) ∉ (((Class.cv (nb067AlphaDummy000))).fv) := by
  simpa only [nb067AlphaDummy163] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy000))).fv) 0

theorem nb067_fresh_037 :
    (nb067AlphaDummy164) ∉ (((Class.cv (nb067AlphaDummy000))).fv) := by
  simpa only [nb067AlphaDummy164] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy000))).fv) 1

theorem nb067_distinct_038 : (nb067AlphaDummy163) ≠ (nb067AlphaDummy164) := by
  simpa only [nb067AlphaDummy163, nb067AlphaDummy164] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_039 :
    (nb067AlphaDummy083) ∉
      (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) :=
  by
  simpa only [nb067AlphaDummy083] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv)
      0

theorem nb067_fresh_040 :
    (nb067AlphaDummy084) ∉
      (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) :=
  by
  simpa only [nb067AlphaDummy084] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv)
      1

theorem nb067_fresh_041 :
    (nb067AlphaDummy085) ∉
      (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) :=
  by
  simpa only [nb067AlphaDummy085] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv)
      2

theorem nb067_distinct_042 : (nb067AlphaDummy083) ≠ (nb067AlphaDummy084) := by
  simpa only [nb067AlphaDummy083, nb067AlphaDummy084] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_043 : (nb067AlphaDummy083) ≠ (nb067AlphaDummy085) := by
  simpa only [nb067AlphaDummy083, nb067AlphaDummy085] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_044 : (nb067AlphaDummy084) ≠ (nb067AlphaDummy085) := by
  simpa only [nb067AlphaDummy084, nb067AlphaDummy085] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_045 :
    (nb067AlphaDummy321) ∉
      (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb067AlphaDummy321] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv) 0

theorem nb067_fresh_046 :
    (nb067AlphaDummy322) ∉
      (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb067AlphaDummy322] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv) 1

theorem nb067_distinct_047 : (nb067AlphaDummy321) ≠ (nb067AlphaDummy322) := by
  simpa only [nb067AlphaDummy321, nb067AlphaDummy322] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_fresh_048 :
    (nb067AlphaDummy015) ∉
      (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv) :=
  by
  simpa only [nb067AlphaDummy015] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv)
      0

theorem nb067_fresh_049 :
    (nb067AlphaDummy016) ∉
      (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv) :=
  by
  simpa only [nb067AlphaDummy016] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv)
      1

theorem nb067_distinct_050 : (nb067AlphaDummy015) ≠ (nb067AlphaDummy016) := by
  simpa only [nb067AlphaDummy015, nb067AlphaDummy016] using
    (freshVar_injective
      (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_051 :
    (nb067AlphaDummy051) ∉ (((Class.cv (nb067AlphaDummy008))).fv) := by
  simpa only [nb067AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy008))).fv) 0

theorem nb067_fresh_052 :
    (nb067AlphaDummy052) ∉ (((Class.cv (nb067AlphaDummy008))).fv) := by
  simpa only [nb067AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy008))).fv) 1

theorem nb067_distinct_053 : (nb067AlphaDummy051) ≠ (nb067AlphaDummy052) := by
  simpa only [nb067AlphaDummy051, nb067AlphaDummy052] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy008))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_054 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy053 x y f) ∉ (((Class.cv (nb067AlphaDummy010 x y f))).fv) := by
  simpa only [nb067AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy010 x y f))).fv) 0

theorem nb067_fresh_055 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy054 x y f) ∉ (((Class.cv (nb067AlphaDummy010 x y f))).fv) := by
  simpa only [nb067AlphaDummy054] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy010 x y f))).fv) 1

theorem nb067_distinct_056 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy053 x y f) ≠ (nb067AlphaDummy054 x y f) := by
  simpa only [nb067AlphaDummy053, nb067AlphaDummy054] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy010 x y f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_057 :
    (nb067AlphaDummy023) ∉ (((Class.cv (nb067AlphaDummy016))).fv) := by
  simpa only [nb067AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy016))).fv) 0

theorem nb067_fresh_058 :
    (nb067AlphaDummy024) ∉ (((Class.cv (nb067AlphaDummy016))).fv) := by
  simpa only [nb067AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy016))).fv) 1

theorem nb067_distinct_059 : (nb067AlphaDummy023) ≠ (nb067AlphaDummy024) := by
  simpa only [nb067AlphaDummy023, nb067AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy016))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_060 (x : Var) (y : Var) :
    (nb067AlphaDummy025 x y) ∉ (((Class.cv (nb067AlphaDummy018 x y))).fv) := by
  simpa only [nb067AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy018 x y))).fv) 0

theorem nb067_fresh_061 (x : Var) (y : Var) :
    (nb067AlphaDummy026 x y) ∉ (((Class.cv (nb067AlphaDummy018 x y))).fv) := by
  simpa only [nb067AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy018 x y))).fv) 1

theorem nb067_distinct_062 (x : Var) (y : Var) :
    (nb067AlphaDummy025 x y) ≠ (nb067AlphaDummy026 x y) := by
  simpa only [nb067AlphaDummy025, nb067AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy018 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_063 :
    (nb067AlphaDummy029) ∉
      (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_064 :
    (nb067AlphaDummy030) ∉
      (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_065 :
    (nb067AlphaDummy031) ∉
      (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_066 : (nb067AlphaDummy029) ≠ (nb067AlphaDummy030) := by
  simpa only [nb067AlphaDummy029, nb067AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_067 : (nb067AlphaDummy029) ≠ (nb067AlphaDummy031) := by
  simpa only [nb067AlphaDummy029, nb067AlphaDummy031] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_068 : (nb067AlphaDummy030) ≠ (nb067AlphaDummy031) := by
  simpa only [nb067AlphaDummy030, nb067AlphaDummy031] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_069 (x : Var) (y : Var) :
    (nb067AlphaDummy032 x y) ∉
      (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_070 (x : Var) (y : Var) :
    (nb067AlphaDummy033 x y) ∉
      (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part004`. -/


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

theorem nb067_fresh_071 (x : Var) (y : Var) :
    (nb067AlphaDummy034 x y) ∉
      (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy034] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_072 (x : Var) (y : Var) :
    (nb067AlphaDummy032 x y) ≠ (nb067AlphaDummy033 x y) := by
  simpa only [nb067AlphaDummy032, nb067AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_distinct_073 (x : Var) (y : Var) :
    (nb067AlphaDummy032 x y) ≠ (nb067AlphaDummy034 x y) := by
  simpa only [nb067AlphaDummy032, nb067AlphaDummy034] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb067_distinct_074 (x : Var) (y : Var) :
    (nb067AlphaDummy033 x y) ≠ (nb067AlphaDummy034 x y) := by
  simpa only [nb067AlphaDummy033, nb067AlphaDummy034] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb067_fresh_075 :
    (nb067AlphaDummy041) ∉
      (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy030))).fv) :=
  by
  simpa only [nb067AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy030))).fv)
      0

theorem nb067_fresh_076 :
    (nb067AlphaDummy037) ∉
      (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv) :=
  by
  simpa only [nb067AlphaDummy037] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv)
      0

theorem nb067_fresh_077 :
    (nb067AlphaDummy043) ∉
      (((Class.cv (nb067AlphaDummy031))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv) :=
  by
  simpa only [nb067AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy031))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv)
      0

theorem nb067_fresh_078 (x : Var) (y : Var) :
    (nb067AlphaDummy042 x y) ∉
      (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb067AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy033 x y))).fv)
      0

theorem nb067_fresh_079 (x : Var) (y : Var) :
    (nb067AlphaDummy038 x y) ∉
      (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy034 x y))).fv) :=
  by
  simpa only [nb067AlphaDummy038] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy034 x y))).fv)
      0

theorem nb067_fresh_080 (x : Var) (y : Var) :
    (nb067AlphaDummy044 x y) ∉
      (((Class.cv (nb067AlphaDummy034 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy034 x y))).fv) :=
  by
  simpa only [nb067AlphaDummy044] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy034 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy034 x y))).fv)
      0

theorem nb067_fresh_081 :
    (nb067AlphaDummy057) ∉
      (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_082 :
    (nb067AlphaDummy058) ∉
      (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_083 :
    (nb067AlphaDummy059) ∉
      (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_084 : (nb067AlphaDummy057) ≠ (nb067AlphaDummy058) := by
  simpa only [nb067AlphaDummy057, nb067AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_085 : (nb067AlphaDummy057) ≠ (nb067AlphaDummy059) := by
  simpa only [nb067AlphaDummy057, nb067AlphaDummy059] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_086 : (nb067AlphaDummy058) ≠ (nb067AlphaDummy059) := by
  simpa only [nb067AlphaDummy058, nb067AlphaDummy059] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_087 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy060 x y f) ∉
      (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_088 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy061 x y f) ∉
      (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_089 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy062 x y f) ∉
      (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_090 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy060 x y f) ≠ (nb067AlphaDummy061 x y f) := by
  simpa only [nb067AlphaDummy060, nb067AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_distinct_091 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy060 x y f) ≠ (nb067AlphaDummy062 x y f) := by
  simpa only [nb067AlphaDummy060, nb067AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb067_distinct_092 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy061 x y f) ≠ (nb067AlphaDummy062 x y f) := by
  simpa only [nb067AlphaDummy061, nb067AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb067_fresh_093 :
    (nb067AlphaDummy069) ∉
      (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy058))).fv) :=
  by
  simpa only [nb067AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy058))).fv)
      0

theorem nb067_fresh_094 :
    (nb067AlphaDummy065) ∉
      (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv) :=
  by
  simpa only [nb067AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv)
      0

theorem nb067_fresh_095 :
    (nb067AlphaDummy071) ∉
      (((Class.cv (nb067AlphaDummy059))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv) :=
  by
  simpa only [nb067AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy059))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv)
      0

theorem nb067_fresh_096 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy070 x y f) ∉
      (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy061 x y f))).fv) :=
  by
  simpa only [nb067AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy061 x y f))).fv)
      0

theorem nb067_fresh_097 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy066 x y f) ∉
      (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy062 x y f))).fv) :=
  by
  simpa only [nb067AlphaDummy066] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy062 x y f))).fv)
      0

theorem nb067_fresh_098 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy072 x y f) ∉
      (((Class.cv (nb067AlphaDummy062 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy062 x y f))).fv) :=
  by
  simpa only [nb067AlphaDummy072] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy062 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy062 x y f))).fv)
      0

theorem nb067_fresh_099 :
    (nb067AlphaDummy091) ∉
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) :=
  by
  simpa only [nb067AlphaDummy091] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv)
      0

theorem nb067_fresh_100 :
    (nb067AlphaDummy092) ∉
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) :=
  by
  simpa only [nb067AlphaDummy092] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv)
      1

theorem nb067_distinct_101 : (nb067AlphaDummy091) ≠ (nb067AlphaDummy092) := by
  simpa only [nb067AlphaDummy091, nb067AlphaDummy092] using
    (freshVar_injective
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_102 :
    (nb067AlphaDummy127) ∉
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv) :=
  by
  simpa only [nb067AlphaDummy127] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv)
      0

theorem nb067_fresh_103 :
    (nb067AlphaDummy128) ∉
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv) :=
  by
  simpa only [nb067AlphaDummy128] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv)
      1

theorem nb067_distinct_104 : (nb067AlphaDummy127) ≠ (nb067AlphaDummy128) := by
  simpa only [nb067AlphaDummy127, nb067AlphaDummy128] using
    (freshVar_injective
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_105 :
    (nb067AlphaDummy241) ∉
      (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) :=
  by
  simpa only [nb067AlphaDummy241] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv)
      0

theorem nb067_fresh_106 :
    (nb067AlphaDummy242) ∉
      (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) :=
  by
  simpa only [nb067AlphaDummy242] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv)
      1

theorem nb067_distinct_107 : (nb067AlphaDummy241) ≠ (nb067AlphaDummy242) := by
  simpa only [nb067AlphaDummy241, nb067AlphaDummy242] using
    (freshVar_injective
      (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_108 (f : Var) :
    (nb067AlphaDummy093 f) ∉
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) :=
  by
  simpa only [nb067AlphaDummy093] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv)
      0

theorem nb067_fresh_109 (f : Var) :
    (nb067AlphaDummy094 f) ∉
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) :=
  by
  simpa only [nb067AlphaDummy094] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv)
      1

theorem nb067_distinct_110 (f : Var) :
    (nb067AlphaDummy093 f) ≠ (nb067AlphaDummy094 f) := by
  simpa only [nb067AlphaDummy093, nb067AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy086 f))).fv ∪
        ((Class.cv (nb067AlphaDummy087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_111 (f : Var) :
    (nb067AlphaDummy129 f) ∉
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy088 f))).fv) :=
  by
  simpa only [nb067AlphaDummy129] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy088 f))).fv)
      0

theorem nb067_fresh_112 (f : Var) :
    (nb067AlphaDummy130 f) ∉
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy088 f))).fv) :=
  by
  simpa only [nb067AlphaDummy130] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy088 f))).fv)
      1

theorem nb067_distinct_113 (f : Var) :
    (nb067AlphaDummy129 f) ≠ (nb067AlphaDummy130 f) := by
  simpa only [nb067AlphaDummy129, nb067AlphaDummy130] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy086 f))).fv ∪
        ((Class.cv (nb067AlphaDummy088 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_114 (f : Var) :
    (nb067AlphaDummy243 f) ∉
      (((Class.cv (nb067AlphaDummy088 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) :=
  by
  simpa only [nb067AlphaDummy243] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy088 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv)
      0

theorem nb067_fresh_115 (f : Var) :
    (nb067AlphaDummy244 f) ∉
      (((Class.cv (nb067AlphaDummy088 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) :=
  by
  simpa only [nb067AlphaDummy244] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy088 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv)
      1

theorem nb067_distinct_116 (f : Var) :
    (nb067AlphaDummy243 f) ≠ (nb067AlphaDummy244 f) := by
  simpa only [nb067AlphaDummy243, nb067AlphaDummy244] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy088 f))).fv ∪
        ((Class.cv (nb067AlphaDummy087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_117 :
    (nb067AlphaDummy099) ∉ (((Class.cv (nb067AlphaDummy092))).fv) := by
  simpa only [nb067AlphaDummy099] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy092))).fv) 0

theorem nb067_fresh_118 :
    (nb067AlphaDummy100) ∉ (((Class.cv (nb067AlphaDummy092))).fv) := by
  simpa only [nb067AlphaDummy100] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy092))).fv) 1

theorem nb067_distinct_119 : (nb067AlphaDummy099) ≠ (nb067AlphaDummy100) := by
  simpa only [nb067AlphaDummy099, nb067AlphaDummy100] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy092))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_120 (f : Var) :
    (nb067AlphaDummy101 f) ∉ (((Class.cv (nb067AlphaDummy094 f))).fv) := by
  simpa only [nb067AlphaDummy101] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy094 f))).fv) 0

theorem nb067_fresh_121 (f : Var) :
    (nb067AlphaDummy102 f) ∉ (((Class.cv (nb067AlphaDummy094 f))).fv) := by
  simpa only [nb067AlphaDummy102] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy094 f))).fv) 1

theorem nb067_distinct_122 (f : Var) :
    (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy102 f) := by
  simpa only [nb067AlphaDummy101, nb067AlphaDummy102] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy094 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_123 :
    (nb067AlphaDummy105) ∉
      (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy105] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_124 :
    (nb067AlphaDummy106) ∉
      (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy106] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_125 :
    (nb067AlphaDummy107) ∉
      (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy107] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_126 : (nb067AlphaDummy105) ≠ (nb067AlphaDummy106) := by
  simpa only [nb067AlphaDummy105, nb067AlphaDummy106] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_127 : (nb067AlphaDummy105) ≠ (nb067AlphaDummy107) := by
  simpa only [nb067AlphaDummy105, nb067AlphaDummy107] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_128 : (nb067AlphaDummy106) ≠ (nb067AlphaDummy107) := by
  simpa only [nb067AlphaDummy106, nb067AlphaDummy107] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_129 (f : Var) :
    (nb067AlphaDummy108 f) ∉
      (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy108] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_130 (f : Var) :
    (nb067AlphaDummy109 f) ∉
      (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy109] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_131 (f : Var) :
    (nb067AlphaDummy110 f) ∉
      (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy110] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_132 (f : Var) :
    (nb067AlphaDummy108 f) ≠ (nb067AlphaDummy109 f) := by
  simpa only [nb067AlphaDummy108, nb067AlphaDummy109] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_133 (f : Var) :
    (nb067AlphaDummy108 f) ≠ (nb067AlphaDummy110 f) := by
  simpa only [nb067AlphaDummy108, nb067AlphaDummy110] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_134 (f : Var) :
    (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy110 f) := by
  simpa only [nb067AlphaDummy109, nb067AlphaDummy110] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_135 :
    (nb067AlphaDummy117) ∉
      (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy106))).fv) :=
  by
  simpa only [nb067AlphaDummy117] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy106))).fv)
      0

theorem nb067_fresh_136 :
    (nb067AlphaDummy113) ∉
      (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv) :=
  by
  simpa only [nb067AlphaDummy113] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv)
      0

theorem nb067_fresh_137 :
    (nb067AlphaDummy119) ∉
      (((Class.cv (nb067AlphaDummy107))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv) :=
  by
  simpa only [nb067AlphaDummy119] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy107))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv)
      0

theorem nb067_fresh_138 (f : Var) :
    (nb067AlphaDummy118 f) ∉
      (((Class.cv (nb067AlphaDummy109 f))).fv ∪ ((Class.cv (nb067AlphaDummy109 f))).fv) :=
  by
  simpa only [nb067AlphaDummy118] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy109 f))).fv ∪ ((Class.cv (nb067AlphaDummy109 f))).fv)
      0

theorem nb067_fresh_139 (f : Var) :
    (nb067AlphaDummy114 f) ∉
      (((Class.cv (nb067AlphaDummy109 f))).fv ∪ ((Class.cv (nb067AlphaDummy110 f))).fv) :=
  by
  simpa only [nb067AlphaDummy114] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy109 f))).fv ∪ ((Class.cv (nb067AlphaDummy110 f))).fv)
      0

theorem nb067_fresh_140 (f : Var) :
    (nb067AlphaDummy120 f) ∉
      (((Class.cv (nb067AlphaDummy110 f))).fv ∪ ((Class.cv (nb067AlphaDummy110 f))).fv) :=
  by
  simpa only [nb067AlphaDummy120] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy110 f))).fv ∪ ((Class.cv (nb067AlphaDummy110 f))).fv)
      0

theorem nb067_fresh_141 :
    (nb067AlphaDummy135) ∉ (((Class.cv (nb067AlphaDummy128))).fv) := by
  simpa only [nb067AlphaDummy135] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy128))).fv) 0

theorem nb067_fresh_142 :
    (nb067AlphaDummy136) ∉ (((Class.cv (nb067AlphaDummy128))).fv) := by
  simpa only [nb067AlphaDummy136] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy128))).fv) 1

theorem nb067_distinct_143 : (nb067AlphaDummy135) ≠ (nb067AlphaDummy136) := by
  simpa only [nb067AlphaDummy135, nb067AlphaDummy136] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy128))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_144 (f : Var) :
    (nb067AlphaDummy137 f) ∉ (((Class.cv (nb067AlphaDummy130 f))).fv) := by
  simpa only [nb067AlphaDummy137] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy130 f))).fv) 0

theorem nb067_fresh_145 (f : Var) :
    (nb067AlphaDummy138 f) ∉ (((Class.cv (nb067AlphaDummy130 f))).fv) := by
  simpa only [nb067AlphaDummy138] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy130 f))).fv) 1

theorem nb067_distinct_146 (f : Var) :
    (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy138 f) := by
  simpa only [nb067AlphaDummy137, nb067AlphaDummy138] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy130 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_147 :
    (nb067AlphaDummy141) ∉
      (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy141] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_148 :
    (nb067AlphaDummy142) ∉
      (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy142] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_149 :
    (nb067AlphaDummy143) ∉
      (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy143] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_150 : (nb067AlphaDummy141) ≠ (nb067AlphaDummy142) := by
  simpa only [nb067AlphaDummy141, nb067AlphaDummy142] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_151 : (nb067AlphaDummy141) ≠ (nb067AlphaDummy143) := by
  simpa only [nb067AlphaDummy141, nb067AlphaDummy143] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_152 : (nb067AlphaDummy142) ≠ (nb067AlphaDummy143) := by
  simpa only [nb067AlphaDummy142, nb067AlphaDummy143] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_153 (f : Var) :
    (nb067AlphaDummy144 f) ∉
      (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy144] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_154 (f : Var) :
    (nb067AlphaDummy145 f) ∉
      (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy145] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_155 (f : Var) :
    (nb067AlphaDummy146 f) ∉
      (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy146] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_156 (f : Var) :
    (nb067AlphaDummy144 f) ≠ (nb067AlphaDummy145 f) := by
  simpa only [nb067AlphaDummy144, nb067AlphaDummy145] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_157 (f : Var) :
    (nb067AlphaDummy144 f) ≠ (nb067AlphaDummy146 f) := by
  simpa only [nb067AlphaDummy144, nb067AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_158 (f : Var) :
    (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy146 f) := by
  simpa only [nb067AlphaDummy145, nb067AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_159 :
    (nb067AlphaDummy153) ∉
      (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy142))).fv) :=
  by
  simpa only [nb067AlphaDummy153] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy142))).fv)
      0

theorem nb067_fresh_160 :
    (nb067AlphaDummy149) ∉
      (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv) :=
  by
  simpa only [nb067AlphaDummy149] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv)
      0

theorem nb067_fresh_161 :
    (nb067AlphaDummy155) ∉
      (((Class.cv (nb067AlphaDummy143))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv) :=
  by
  simpa only [nb067AlphaDummy155] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy143))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv)
      0

theorem nb067_fresh_162 (f : Var) :
    (nb067AlphaDummy154 f) ∉
      (((Class.cv (nb067AlphaDummy145 f))).fv ∪ ((Class.cv (nb067AlphaDummy145 f))).fv) :=
  by
  simpa only [nb067AlphaDummy154] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy145 f))).fv ∪ ((Class.cv (nb067AlphaDummy145 f))).fv)
      0

theorem nb067_fresh_163 (f : Var) :
    (nb067AlphaDummy150 f) ∉
      (((Class.cv (nb067AlphaDummy145 f))).fv ∪ ((Class.cv (nb067AlphaDummy146 f))).fv) :=
  by
  simpa only [nb067AlphaDummy150] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy145 f))).fv ∪ ((Class.cv (nb067AlphaDummy146 f))).fv)
      0

theorem nb067_fresh_164 (f : Var) :
    (nb067AlphaDummy156 f) ∉
      (((Class.cv (nb067AlphaDummy146 f))).fv ∪ ((Class.cv (nb067AlphaDummy146 f))).fv) :=
  by
  simpa only [nb067AlphaDummy156] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy146 f))).fv ∪ ((Class.cv (nb067AlphaDummy146 f))).fv)
      0

theorem nb067_fresh_165 :
    (nb067AlphaDummy169) ∉
      (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv) :=
  by
  simpa only [nb067AlphaDummy169] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv)
      0

theorem nb067_fresh_166 :
    (nb067AlphaDummy170) ∉
      (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv) :=
  by
  simpa only [nb067AlphaDummy170] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv)
      1

theorem nb067_distinct_167 : (nb067AlphaDummy169) ≠ (nb067AlphaDummy170) := by
  simpa only [nb067AlphaDummy169, nb067AlphaDummy170] using
    (freshVar_injective
      (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_168 :
    (nb067AlphaDummy205) ∉
      (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv) :=
  by
  simpa only [nb067AlphaDummy205] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv)
      0

theorem nb067_fresh_169 :
    (nb067AlphaDummy206) ∉
      (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv) :=
  by
  simpa only [nb067AlphaDummy206] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv)
      1

theorem nb067_distinct_170 : (nb067AlphaDummy205) ≠ (nb067AlphaDummy206) := by
  simpa only [nb067AlphaDummy205, nb067AlphaDummy206] using
    (freshVar_injective
      (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_171 (f : Var) :
    (nb067AlphaDummy171 f) ∉
      (((Class.cv (nb067AlphaDummy165 f))).fv ∪ ((Class.cv (nb067AlphaDummy166 f))).fv) :=
  by
  simpa only [nb067AlphaDummy171] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy165 f))).fv ∪ ((Class.cv (nb067AlphaDummy166 f))).fv)
      0

theorem nb067_fresh_172 (f : Var) :
    (nb067AlphaDummy172 f) ∉
      (((Class.cv (nb067AlphaDummy165 f))).fv ∪ ((Class.cv (nb067AlphaDummy166 f))).fv) :=
  by
  simpa only [nb067AlphaDummy172] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy165 f))).fv ∪ ((Class.cv (nb067AlphaDummy166 f))).fv)
      1

theorem nb067_distinct_173 (f : Var) :
    (nb067AlphaDummy171 f) ≠ (nb067AlphaDummy172 f) := by
  simpa only [nb067AlphaDummy171, nb067AlphaDummy172] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy165 f))).fv ∪
        ((Class.cv (nb067AlphaDummy166 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_174 (f : Var) :
    (nb067AlphaDummy207 f) ∉
      (((Class.cv (nb067AlphaDummy166 f))).fv ∪ ((Class.cv (nb067AlphaDummy165 f))).fv) :=
  by
  simpa only [nb067AlphaDummy207] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy166 f))).fv ∪ ((Class.cv (nb067AlphaDummy165 f))).fv)
      0

theorem nb067_fresh_175 (f : Var) :
    (nb067AlphaDummy208 f) ∉
      (((Class.cv (nb067AlphaDummy166 f))).fv ∪ ((Class.cv (nb067AlphaDummy165 f))).fv) :=
  by
  simpa only [nb067AlphaDummy208] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy166 f))).fv ∪ ((Class.cv (nb067AlphaDummy165 f))).fv)
      1

theorem nb067_distinct_176 (f : Var) :
    (nb067AlphaDummy207 f) ≠ (nb067AlphaDummy208 f) := by
  simpa only [nb067AlphaDummy207, nb067AlphaDummy208] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy166 f))).fv ∪
        ((Class.cv (nb067AlphaDummy165 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_177 :
    (nb067AlphaDummy177) ∉ (((Class.cv (nb067AlphaDummy170))).fv) := by
  simpa only [nb067AlphaDummy177] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy170))).fv) 0

theorem nb067_fresh_178 :
    (nb067AlphaDummy178) ∉ (((Class.cv (nb067AlphaDummy170))).fv) := by
  simpa only [nb067AlphaDummy178] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy170))).fv) 1

theorem nb067_distinct_179 : (nb067AlphaDummy177) ≠ (nb067AlphaDummy178) := by
  simpa only [nb067AlphaDummy177, nb067AlphaDummy178] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy170))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_180 (f : Var) :
    (nb067AlphaDummy179 f) ∉ (((Class.cv (nb067AlphaDummy172 f))).fv) := by
  simpa only [nb067AlphaDummy179] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy172 f))).fv) 0

theorem nb067_fresh_181 (f : Var) :
    (nb067AlphaDummy180 f) ∉ (((Class.cv (nb067AlphaDummy172 f))).fv) := by
  simpa only [nb067AlphaDummy180] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy172 f))).fv) 1

theorem nb067_distinct_182 (f : Var) :
    (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy180 f) := by
  simpa only [nb067AlphaDummy179, nb067AlphaDummy180] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy172 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_183 :
    (nb067AlphaDummy183) ∉
      (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy183] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_184 :
    (nb067AlphaDummy184) ∉
      (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy184] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_185 :
    (nb067AlphaDummy185) ∉
      (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy185] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_186 : (nb067AlphaDummy183) ≠ (nb067AlphaDummy184) := by
  simpa only [nb067AlphaDummy183, nb067AlphaDummy184] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_187 : (nb067AlphaDummy183) ≠ (nb067AlphaDummy185) := by
  simpa only [nb067AlphaDummy183, nb067AlphaDummy185] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_188 : (nb067AlphaDummy184) ≠ (nb067AlphaDummy185) := by
  simpa only [nb067AlphaDummy184, nb067AlphaDummy185] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_189 (f : Var) :
    (nb067AlphaDummy186 f) ∉
      (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy186] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_190 (f : Var) :
    (nb067AlphaDummy187 f) ∉
      (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy187] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_191 (f : Var) :
    (nb067AlphaDummy188 f) ∉
      (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy188] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_192 (f : Var) :
    (nb067AlphaDummy186 f) ≠ (nb067AlphaDummy187 f) := by
  simpa only [nb067AlphaDummy186, nb067AlphaDummy187] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_193 (f : Var) :
    (nb067AlphaDummy186 f) ≠ (nb067AlphaDummy188 f) := by
  simpa only [nb067AlphaDummy186, nb067AlphaDummy188] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_194 (f : Var) :
    (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy188 f) := by
  simpa only [nb067AlphaDummy187, nb067AlphaDummy188] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_195 :
    (nb067AlphaDummy195) ∉
      (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy184))).fv) :=
  by
  simpa only [nb067AlphaDummy195] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy184))).fv)
      0

theorem nb067_fresh_196 :
    (nb067AlphaDummy191) ∉
      (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv) :=
  by
  simpa only [nb067AlphaDummy191] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv)
      0

theorem nb067_fresh_197 :
    (nb067AlphaDummy197) ∉
      (((Class.cv (nb067AlphaDummy185))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv) :=
  by
  simpa only [nb067AlphaDummy197] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy185))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv)
      0

theorem nb067_fresh_198 (f : Var) :
    (nb067AlphaDummy196 f) ∉
      (((Class.cv (nb067AlphaDummy187 f))).fv ∪ ((Class.cv (nb067AlphaDummy187 f))).fv) :=
  by
  simpa only [nb067AlphaDummy196] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy187 f))).fv ∪ ((Class.cv (nb067AlphaDummy187 f))).fv)
      0

theorem nb067_fresh_199 (f : Var) :
    (nb067AlphaDummy192 f) ∉
      (((Class.cv (nb067AlphaDummy187 f))).fv ∪ ((Class.cv (nb067AlphaDummy188 f))).fv) :=
  by
  simpa only [nb067AlphaDummy192] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy187 f))).fv ∪ ((Class.cv (nb067AlphaDummy188 f))).fv)
      0

theorem nb067_fresh_200 (f : Var) :
    (nb067AlphaDummy198 f) ∉
      (((Class.cv (nb067AlphaDummy188 f))).fv ∪ ((Class.cv (nb067AlphaDummy188 f))).fv) :=
  by
  simpa only [nb067AlphaDummy198] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy188 f))).fv ∪ ((Class.cv (nb067AlphaDummy188 f))).fv)
      0

theorem nb067_fresh_201 :
    (nb067AlphaDummy213) ∉ (((Class.cv (nb067AlphaDummy206))).fv) := by
  simpa only [nb067AlphaDummy213] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy206))).fv) 0

theorem nb067_fresh_202 :
    (nb067AlphaDummy214) ∉ (((Class.cv (nb067AlphaDummy206))).fv) := by
  simpa only [nb067AlphaDummy214] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy206))).fv) 1

theorem nb067_distinct_203 : (nb067AlphaDummy213) ≠ (nb067AlphaDummy214) := by
  simpa only [nb067AlphaDummy213, nb067AlphaDummy214] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy206))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_204 (f : Var) :
    (nb067AlphaDummy215 f) ∉ (((Class.cv (nb067AlphaDummy208 f))).fv) := by
  simpa only [nb067AlphaDummy215] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy208 f))).fv) 0

theorem nb067_fresh_205 (f : Var) :
    (nb067AlphaDummy216 f) ∉ (((Class.cv (nb067AlphaDummy208 f))).fv) := by
  simpa only [nb067AlphaDummy216] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy208 f))).fv) 1

theorem nb067_distinct_206 (f : Var) :
    (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy216 f) := by
  simpa only [nb067AlphaDummy215, nb067AlphaDummy216] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy208 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_207 :
    (nb067AlphaDummy219) ∉
      (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy219] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_208 :
    (nb067AlphaDummy220) ∉
      (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy220] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_209 :
    (nb067AlphaDummy221) ∉
      (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy221] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_210 : (nb067AlphaDummy219) ≠ (nb067AlphaDummy220) := by
  simpa only [nb067AlphaDummy219, nb067AlphaDummy220] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_211 : (nb067AlphaDummy219) ≠ (nb067AlphaDummy221) := by
  simpa only [nb067AlphaDummy219, nb067AlphaDummy221] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_212 : (nb067AlphaDummy220) ≠ (nb067AlphaDummy221) := by
  simpa only [nb067AlphaDummy220, nb067AlphaDummy221] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_213 (f : Var) :
    (nb067AlphaDummy222 f) ∉
      (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy222] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_214 (f : Var) :
    (nb067AlphaDummy223 f) ∉
      (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy223] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_215 (f : Var) :
    (nb067AlphaDummy224 f) ∉
      (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy224] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_216 (f : Var) :
    (nb067AlphaDummy222 f) ≠ (nb067AlphaDummy223 f) := by
  simpa only [nb067AlphaDummy222, nb067AlphaDummy223] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_217 (f : Var) :
    (nb067AlphaDummy222 f) ≠ (nb067AlphaDummy224 f) := by
  simpa only [nb067AlphaDummy222, nb067AlphaDummy224] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_218 (f : Var) :
    (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy224 f) := by
  simpa only [nb067AlphaDummy223, nb067AlphaDummy224] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_219 :
    (nb067AlphaDummy231) ∉
      (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy220))).fv) :=
  by
  simpa only [nb067AlphaDummy231] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy220))).fv)
      0

theorem nb067_fresh_220 :
    (nb067AlphaDummy227) ∉
      (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv) :=
  by
  simpa only [nb067AlphaDummy227] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part005`. -/


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

theorem nb067_fresh_221 :
    (nb067AlphaDummy233) ∉
      (((Class.cv (nb067AlphaDummy221))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv) :=
  by
  simpa only [nb067AlphaDummy233] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy221))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv)
      0

theorem nb067_fresh_222 (f : Var) :
    (nb067AlphaDummy232 f) ∉
      (((Class.cv (nb067AlphaDummy223 f))).fv ∪ ((Class.cv (nb067AlphaDummy223 f))).fv) :=
  by
  simpa only [nb067AlphaDummy232] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy223 f))).fv ∪ ((Class.cv (nb067AlphaDummy223 f))).fv)
      0

theorem nb067_fresh_223 (f : Var) :
    (nb067AlphaDummy228 f) ∉
      (((Class.cv (nb067AlphaDummy223 f))).fv ∪ ((Class.cv (nb067AlphaDummy224 f))).fv) :=
  by
  simpa only [nb067AlphaDummy228] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy223 f))).fv ∪ ((Class.cv (nb067AlphaDummy224 f))).fv)
      0

theorem nb067_fresh_224 (f : Var) :
    (nb067AlphaDummy234 f) ∉
      (((Class.cv (nb067AlphaDummy224 f))).fv ∪ ((Class.cv (nb067AlphaDummy224 f))).fv) :=
  by
  simpa only [nb067AlphaDummy234] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy224 f))).fv ∪ ((Class.cv (nb067AlphaDummy224 f))).fv)
      0

theorem nb067_fresh_225 :
    (nb067AlphaDummy249) ∉ (((Class.cv (nb067AlphaDummy242))).fv) := by
  simpa only [nb067AlphaDummy249] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy242))).fv) 0

theorem nb067_fresh_226 :
    (nb067AlphaDummy250) ∉ (((Class.cv (nb067AlphaDummy242))).fv) := by
  simpa only [nb067AlphaDummy250] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy242))).fv) 1

theorem nb067_distinct_227 : (nb067AlphaDummy249) ≠ (nb067AlphaDummy250) := by
  simpa only [nb067AlphaDummy249, nb067AlphaDummy250] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy242))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_228 (f : Var) :
    (nb067AlphaDummy251 f) ∉ (((Class.cv (nb067AlphaDummy244 f))).fv) := by
  simpa only [nb067AlphaDummy251] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy244 f))).fv) 0

theorem nb067_fresh_229 (f : Var) :
    (nb067AlphaDummy252 f) ∉ (((Class.cv (nb067AlphaDummy244 f))).fv) := by
  simpa only [nb067AlphaDummy252] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy244 f))).fv) 1

theorem nb067_distinct_230 (f : Var) :
    (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy252 f) := by
  simpa only [nb067AlphaDummy251, nb067AlphaDummy252] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy244 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_231 :
    (nb067AlphaDummy255) ∉
      (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy255] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_232 :
    (nb067AlphaDummy256) ∉
      (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy256] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_233 :
    (nb067AlphaDummy257) ∉
      (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy257] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_234 : (nb067AlphaDummy255) ≠ (nb067AlphaDummy256) := by
  simpa only [nb067AlphaDummy255, nb067AlphaDummy256] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_235 : (nb067AlphaDummy255) ≠ (nb067AlphaDummy257) := by
  simpa only [nb067AlphaDummy255, nb067AlphaDummy257] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_236 : (nb067AlphaDummy256) ≠ (nb067AlphaDummy257) := by
  simpa only [nb067AlphaDummy256, nb067AlphaDummy257] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_237 (f : Var) :
    (nb067AlphaDummy258 f) ∉
      (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy258] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_238 (f : Var) :
    (nb067AlphaDummy259 f) ∉
      (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy259] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_239 (f : Var) :
    (nb067AlphaDummy260 f) ∉
      (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy260] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_240 (f : Var) :
    (nb067AlphaDummy258 f) ≠ (nb067AlphaDummy259 f) := by
  simpa only [nb067AlphaDummy258, nb067AlphaDummy259] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_241 (f : Var) :
    (nb067AlphaDummy258 f) ≠ (nb067AlphaDummy260 f) := by
  simpa only [nb067AlphaDummy258, nb067AlphaDummy260] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_242 (f : Var) :
    (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy260 f) := by
  simpa only [nb067AlphaDummy259, nb067AlphaDummy260] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_243 :
    (nb067AlphaDummy267) ∉
      (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy256))).fv) :=
  by
  simpa only [nb067AlphaDummy267] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy256))).fv)
      0

theorem nb067_fresh_244 :
    (nb067AlphaDummy263) ∉
      (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv) :=
  by
  simpa only [nb067AlphaDummy263] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv)
      0

theorem nb067_fresh_245 :
    (nb067AlphaDummy269) ∉
      (((Class.cv (nb067AlphaDummy257))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv) :=
  by
  simpa only [nb067AlphaDummy269] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy257))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv)
      0

theorem nb067_fresh_246 (f : Var) :
    (nb067AlphaDummy268 f) ∉
      (((Class.cv (nb067AlphaDummy259 f))).fv ∪ ((Class.cv (nb067AlphaDummy259 f))).fv) :=
  by
  simpa only [nb067AlphaDummy268] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy259 f))).fv ∪ ((Class.cv (nb067AlphaDummy259 f))).fv)
      0

theorem nb067_fresh_247 (f : Var) :
    (nb067AlphaDummy264 f) ∉
      (((Class.cv (nb067AlphaDummy259 f))).fv ∪ ((Class.cv (nb067AlphaDummy260 f))).fv) :=
  by
  simpa only [nb067AlphaDummy264] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy259 f))).fv ∪ ((Class.cv (nb067AlphaDummy260 f))).fv)
      0

theorem nb067_fresh_248 (f : Var) :
    (nb067AlphaDummy270 f) ∉
      (((Class.cv (nb067AlphaDummy260 f))).fv ∪ ((Class.cv (nb067AlphaDummy260 f))).fv) :=
  by
  simpa only [nb067AlphaDummy270] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy260 f))).fv ∪ ((Class.cv (nb067AlphaDummy260 f))).fv)
      0

theorem nb067_fresh_249 :
    (nb067AlphaDummy281) ∉
      (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv) :=
  by
  simpa only [nb067AlphaDummy281] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv)
      0

theorem nb067_fresh_250 :
    (nb067AlphaDummy282) ∉
      (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv) :=
  by
  simpa only [nb067AlphaDummy282] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv)
      1

theorem nb067_distinct_251 : (nb067AlphaDummy281) ≠ (nb067AlphaDummy282) := by
  simpa only [nb067AlphaDummy281, nb067AlphaDummy282] using
    (freshVar_injective
      (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_252 (f : Var) :
    (nb067AlphaDummy283 f) ∉
      (((Class.cv (nb067AlphaDummy280 f))).fv ∪ ((Class.cv (nb067AlphaDummy279 f))).fv) :=
  by
  simpa only [nb067AlphaDummy283] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy280 f))).fv ∪ ((Class.cv (nb067AlphaDummy279 f))).fv)
      0

theorem nb067_fresh_253 (f : Var) :
    (nb067AlphaDummy284 f) ∉
      (((Class.cv (nb067AlphaDummy280 f))).fv ∪ ((Class.cv (nb067AlphaDummy279 f))).fv) :=
  by
  simpa only [nb067AlphaDummy284] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy280 f))).fv ∪ ((Class.cv (nb067AlphaDummy279 f))).fv)
      1

theorem nb067_distinct_254 (f : Var) :
    (nb067AlphaDummy283 f) ≠ (nb067AlphaDummy284 f) := by
  simpa only [nb067AlphaDummy283, nb067AlphaDummy284] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy280 f))).fv ∪
        ((Class.cv (nb067AlphaDummy279 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_255 :
    (nb067AlphaDummy289) ∉ (((Class.cv (nb067AlphaDummy282))).fv) := by
  simpa only [nb067AlphaDummy289] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy282))).fv) 0

theorem nb067_fresh_256 :
    (nb067AlphaDummy290) ∉ (((Class.cv (nb067AlphaDummy282))).fv) := by
  simpa only [nb067AlphaDummy290] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy282))).fv) 1

theorem nb067_distinct_257 : (nb067AlphaDummy289) ≠ (nb067AlphaDummy290) := by
  simpa only [nb067AlphaDummy289, nb067AlphaDummy290] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy282))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_258 (f : Var) :
    (nb067AlphaDummy291 f) ∉ (((Class.cv (nb067AlphaDummy284 f))).fv) := by
  simpa only [nb067AlphaDummy291] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy284 f))).fv) 0

theorem nb067_fresh_259 (f : Var) :
    (nb067AlphaDummy292 f) ∉ (((Class.cv (nb067AlphaDummy284 f))).fv) := by
  simpa only [nb067AlphaDummy292] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy284 f))).fv) 1

theorem nb067_distinct_260 (f : Var) :
    (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy292 f) := by
  simpa only [nb067AlphaDummy291, nb067AlphaDummy292] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy284 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_261 :
    (nb067AlphaDummy295) ∉
      (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy295] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_262 :
    (nb067AlphaDummy296) ∉
      (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy296] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_263 :
    (nb067AlphaDummy297) ∉
      (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy297] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_264 : (nb067AlphaDummy295) ≠ (nb067AlphaDummy296) := by
  simpa only [nb067AlphaDummy295, nb067AlphaDummy296] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_265 : (nb067AlphaDummy295) ≠ (nb067AlphaDummy297) := by
  simpa only [nb067AlphaDummy295, nb067AlphaDummy297] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_266 : (nb067AlphaDummy296) ≠ (nb067AlphaDummy297) := by
  simpa only [nb067AlphaDummy296, nb067AlphaDummy297] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_267 (f : Var) :
    (nb067AlphaDummy298 f) ∉
      (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy298] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_268 (f : Var) :
    (nb067AlphaDummy299 f) ∉
      (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy299] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_269 (f : Var) :
    (nb067AlphaDummy300 f) ∉
      (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy300] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_270 (f : Var) :
    (nb067AlphaDummy298 f) ≠ (nb067AlphaDummy299 f) := by
  simpa only [nb067AlphaDummy298, nb067AlphaDummy299] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_271 (f : Var) :
    (nb067AlphaDummy298 f) ≠ (nb067AlphaDummy300 f) := by
  simpa only [nb067AlphaDummy298, nb067AlphaDummy300] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_272 (f : Var) :
    (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy300 f) := by
  simpa only [nb067AlphaDummy299, nb067AlphaDummy300] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_273 :
    (nb067AlphaDummy307) ∉
      (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy296))).fv) :=
  by
  simpa only [nb067AlphaDummy307] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy296))).fv)
      0

theorem nb067_fresh_274 :
    (nb067AlphaDummy303) ∉
      (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv) :=
  by
  simpa only [nb067AlphaDummy303] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv)
      0

theorem nb067_fresh_275 :
    (nb067AlphaDummy309) ∉
      (((Class.cv (nb067AlphaDummy297))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv) :=
  by
  simpa only [nb067AlphaDummy309] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy297))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv)
      0

theorem nb067_fresh_276 (f : Var) :
    (nb067AlphaDummy308 f) ∉
      (((Class.cv (nb067AlphaDummy299 f))).fv ∪ ((Class.cv (nb067AlphaDummy299 f))).fv) :=
  by
  simpa only [nb067AlphaDummy308] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy299 f))).fv ∪ ((Class.cv (nb067AlphaDummy299 f))).fv)
      0

theorem nb067_fresh_277 (f : Var) :
    (nb067AlphaDummy304 f) ∉
      (((Class.cv (nb067AlphaDummy299 f))).fv ∪ ((Class.cv (nb067AlphaDummy300 f))).fv) :=
  by
  simpa only [nb067AlphaDummy304] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy299 f))).fv ∪ ((Class.cv (nb067AlphaDummy300 f))).fv)
      0

theorem nb067_fresh_278 (f : Var) :
    (nb067AlphaDummy310 f) ∉
      (((Class.cv (nb067AlphaDummy300 f))).fv ∪ ((Class.cv (nb067AlphaDummy300 f))).fv) :=
  by
  simpa only [nb067AlphaDummy310] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy300 f))).fv ∪ ((Class.cv (nb067AlphaDummy300 f))).fv)
      0

theorem nb067_fresh_279 :
    (nb067AlphaDummy325) ∉
      (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv) :=
  by
  simpa only [nb067AlphaDummy325] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv)
      0

theorem nb067_fresh_280 :
    (nb067AlphaDummy326) ∉
      (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv) :=
  by
  simpa only [nb067AlphaDummy326] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv)
      1

theorem nb067_distinct_281 : (nb067AlphaDummy325) ≠ (nb067AlphaDummy326) := by
  simpa only [nb067AlphaDummy325, nb067AlphaDummy326] using
    (freshVar_injective
      (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_282 (f : Var) :
    (nb067AlphaDummy327 f) ∉
      (((Class.cv (nb067AlphaDummy324 f))).fv ∪ ((Class.cv (nb067AlphaDummy323 f))).fv) :=
  by
  simpa only [nb067AlphaDummy327] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy324 f))).fv ∪ ((Class.cv (nb067AlphaDummy323 f))).fv)
      0

theorem nb067_fresh_283 (f : Var) :
    (nb067AlphaDummy328 f) ∉
      (((Class.cv (nb067AlphaDummy324 f))).fv ∪ ((Class.cv (nb067AlphaDummy323 f))).fv) :=
  by
  simpa only [nb067AlphaDummy328] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy324 f))).fv ∪ ((Class.cv (nb067AlphaDummy323 f))).fv)
      1

theorem nb067_distinct_284 (f : Var) :
    (nb067AlphaDummy327 f) ≠ (nb067AlphaDummy328 f) := by
  simpa only [nb067AlphaDummy327, nb067AlphaDummy328] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy324 f))).fv ∪
        ((Class.cv (nb067AlphaDummy323 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_285 :
    (nb067AlphaDummy333) ∉ (((Class.cv (nb067AlphaDummy326))).fv) := by
  simpa only [nb067AlphaDummy333] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy326))).fv) 0

theorem nb067_fresh_286 :
    (nb067AlphaDummy334) ∉ (((Class.cv (nb067AlphaDummy326))).fv) := by
  simpa only [nb067AlphaDummy334] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy326))).fv) 1

theorem nb067_distinct_287 : (nb067AlphaDummy333) ≠ (nb067AlphaDummy334) := by
  simpa only [nb067AlphaDummy333, nb067AlphaDummy334] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy326))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_288 (f : Var) :
    (nb067AlphaDummy335 f) ∉ (((Class.cv (nb067AlphaDummy328 f))).fv) := by
  simpa only [nb067AlphaDummy335] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy328 f))).fv) 0

theorem nb067_fresh_289 (f : Var) :
    (nb067AlphaDummy336 f) ∉ (((Class.cv (nb067AlphaDummy328 f))).fv) := by
  simpa only [nb067AlphaDummy336] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy328 f))).fv) 1

theorem nb067_distinct_290 (f : Var) :
    (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy336 f) := by
  simpa only [nb067AlphaDummy335, nb067AlphaDummy336] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy328 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_291 :
    (nb067AlphaDummy339) ∉
      (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy339] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_292 :
    (nb067AlphaDummy340) ∉
      (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy340] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_293 :
    (nb067AlphaDummy341) ∉
      (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy341] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_294 : (nb067AlphaDummy339) ≠ (nb067AlphaDummy340) := by
  simpa only [nb067AlphaDummy339, nb067AlphaDummy340] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_295 : (nb067AlphaDummy339) ≠ (nb067AlphaDummy341) := by
  simpa only [nb067AlphaDummy339, nb067AlphaDummy341] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_296 : (nb067AlphaDummy340) ≠ (nb067AlphaDummy341) := by
  simpa only [nb067AlphaDummy340, nb067AlphaDummy341] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_297 (f : Var) :
    (nb067AlphaDummy342 f) ∉
      (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy342] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) 0

theorem nb067_fresh_298 (f : Var) :
    (nb067AlphaDummy343 f) ∉
      (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy343] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) 1

theorem nb067_fresh_299 (f : Var) :
    (nb067AlphaDummy344 f) ∉
      (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb067AlphaDummy344] using
    freshVar_not_mem (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) 2

theorem nb067_distinct_300 (f : Var) :
    (nb067AlphaDummy342 f) ≠ (nb067AlphaDummy343 f) := by
  simpa only [nb067AlphaDummy342, nb067AlphaDummy343] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb067_distinct_301 (f : Var) :
    (nb067AlphaDummy342 f) ≠ (nb067AlphaDummy344 f) := by
  simpa only [nb067AlphaDummy342, nb067AlphaDummy344] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb067_distinct_302 (f : Var) :
    (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy344 f) := by
  simpa only [nb067AlphaDummy343, nb067AlphaDummy344] using
    (freshVar_injective (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb067_fresh_303 :
    (nb067AlphaDummy351) ∉
      (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy340))).fv) :=
  by
  simpa only [nb067AlphaDummy351] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy340))).fv)
      0

theorem nb067_fresh_304 :
    (nb067AlphaDummy347) ∉
      (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv) :=
  by
  simpa only [nb067AlphaDummy347] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy340))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv)
      0

theorem nb067_fresh_305 :
    (nb067AlphaDummy353) ∉
      (((Class.cv (nb067AlphaDummy341))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv) :=
  by
  simpa only [nb067AlphaDummy353] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy341))).fv ∪ ((Class.cv (nb067AlphaDummy341))).fv)
      0

theorem nb067_fresh_306 (f : Var) :
    (nb067AlphaDummy352 f) ∉
      (((Class.cv (nb067AlphaDummy343 f))).fv ∪ ((Class.cv (nb067AlphaDummy343 f))).fv) :=
  by
  simpa only [nb067AlphaDummy352] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy343 f))).fv ∪ ((Class.cv (nb067AlphaDummy343 f))).fv)
      0

theorem nb067_fresh_307 (f : Var) :
    (nb067AlphaDummy348 f) ∉
      (((Class.cv (nb067AlphaDummy343 f))).fv ∪ ((Class.cv (nb067AlphaDummy344 f))).fv) :=
  by
  simpa only [nb067AlphaDummy348] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy343 f))).fv ∪ ((Class.cv (nb067AlphaDummy344 f))).fv)
      0

theorem nb067_fresh_308 (f : Var) :
    (nb067AlphaDummy354 f) ∉
      (((Class.cv (nb067AlphaDummy344 f))).fv ∪ ((Class.cv (nb067AlphaDummy344 f))).fv) :=
  by
  simpa only [nb067AlphaDummy354] using
    freshVar_not_mem
      (((Class.cv (nb067AlphaDummy344 f))).fv ∪ ((Class.cv (nb067AlphaDummy344 f))).fv)
      0

theorem nb067_fresh_309 (f : Var) : (nb067AlphaDummy165 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb067AlphaDummy165] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb067_fresh_310 (f : Var) : (nb067AlphaDummy166 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb067AlphaDummy166] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb067_distinct_311 (f : Var) :
    (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy166 f) := by
  simpa only [nb067AlphaDummy165, nb067AlphaDummy166] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_312 (f : Var) :
    (nb067AlphaDummy086 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb067AlphaDummy086] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0

theorem nb067_fresh_313 (f : Var) :
    (nb067AlphaDummy087 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb067AlphaDummy087] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1

theorem nb067_fresh_314 (f : Var) :
    (nb067AlphaDummy088 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb067AlphaDummy088] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2

theorem nb067_distinct_315 (f : Var) :
    (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy087 f) := by
  simpa only [nb067AlphaDummy086, nb067AlphaDummy087] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb067_distinct_316 (f : Var) :
    (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy088 f) := by
  simpa only [nb067AlphaDummy086, nb067AlphaDummy088] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb067_distinct_317 (f : Var) :
    (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy088 f) := by
  simpa only [nb067AlphaDummy087, nb067AlphaDummy088] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb067_fresh_318 (f : Var) :
    (nb067AlphaDummy323 f) ∉ (((Class.cv f)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb067AlphaDummy323] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCvv)).fv) 0

theorem nb067_fresh_319 (f : Var) :
    (nb067AlphaDummy324 f) ∉ (((Class.cv f)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb067AlphaDummy324] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCvv)).fv) 1

theorem nb067_distinct_320 (f : Var) :
    (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy324 f) := by
  simpa only [nb067AlphaDummy323, nb067AlphaDummy324] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_321 (x : Var) (y : Var) :
    (nb067AlphaDummy017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb067AlphaDummy017] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb067_fresh_322 (x : Var) (y : Var) :
    (nb067AlphaDummy018 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb067AlphaDummy018] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb067_distinct_323 (x : Var) (y : Var) :
    (nb067AlphaDummy017 x y) ≠ (nb067AlphaDummy018 x y) := by
  simpa only [nb067AlphaDummy017, nb067AlphaDummy018] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_324 :
    (nb067AlphaDummy027) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy023)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy023)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy023))).fv) :=
  by
  simpa only [nb067AlphaDummy027] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy023)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy023)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy023))).fv)
      0

theorem nb067_fresh_325 (x : Var) (y : Var) :
    (nb067AlphaDummy028 x y) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy025 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy025 x y)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy025 x y))).fv) :=
  by
  simpa only [nb067AlphaDummy028] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy025 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy025 x y)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy025 x y))).fv)
      0

theorem nb067_fresh_326 :
    (nb067AlphaDummy055) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy051)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy051)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy051))).fv) :=
  by
  simpa only [nb067AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy051)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy051)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy051))).fv)
      0

theorem nb067_fresh_327 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy056 x y f) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy053 x y f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy053 x y f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy053 x y f))).fv) :=
  by
  simpa only [nb067AlphaDummy056] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy053 x y f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy053 x y f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy053 x y f))).fv)
      0

theorem nb067_fresh_328 :
    (nb067AlphaDummy103) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy099)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy099)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy099))).fv) :=
  by
  simpa only [nb067AlphaDummy103] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy099)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy099)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy099))).fv)
      0

theorem nb067_fresh_329 (f : Var) :
    (nb067AlphaDummy104 f) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy101 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy101 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy101 f))).fv) :=
  by
  simpa only [nb067AlphaDummy104] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy101 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy101 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy101 f))).fv)
      0

theorem nb067_fresh_330 :
    (nb067AlphaDummy139) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy135)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy135)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy135))).fv) :=
  by
  simpa only [nb067AlphaDummy139] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy135)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy135)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy135))).fv)
      0

theorem nb067_fresh_331 (f : Var) :
    (nb067AlphaDummy140 f) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy137 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy137 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy137 f))).fv) :=
  by
  simpa only [nb067AlphaDummy140] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy137 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy137 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy137 f))).fv)
      0

theorem nb067_fresh_332 :
    (nb067AlphaDummy181) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy177))).fv) :=
  by
  simpa only [nb067AlphaDummy181] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy177))).fv)
      0

theorem nb067_fresh_333 (f : Var) :
    (nb067AlphaDummy182 f) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy179 f))).fv) :=
  by
  simpa only [nb067AlphaDummy182] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy179 f))).fv)
      0

theorem nb067_fresh_334 :
    (nb067AlphaDummy217) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy213))).fv) :=
  by
  simpa only [nb067AlphaDummy217] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy213))).fv)
      0

theorem nb067_fresh_335 (f : Var) :
    (nb067AlphaDummy218 f) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy215 f))).fv) :=
  by
  simpa only [nb067AlphaDummy218] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy215 f))).fv)
      0

theorem nb067_fresh_336 :
    (nb067AlphaDummy253) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy249)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy249)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy249))).fv) :=
  by
  simpa only [nb067AlphaDummy253] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy249)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy249)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy249))).fv)
      0

theorem nb067_fresh_337 (f : Var) :
    (nb067AlphaDummy254 f) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy251 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy251 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy251 f))).fv) :=
  by
  simpa only [nb067AlphaDummy254] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy251 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy251 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy251 f))).fv)
      0

theorem nb067_fresh_338 :
    (nb067AlphaDummy293) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy289)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy289)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy289))).fv) :=
  by
  simpa only [nb067AlphaDummy293] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy289)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy289)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy289))).fv)
      0

theorem nb067_fresh_339 (f : Var) :
    (nb067AlphaDummy294 f) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy291 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy291 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy291 f))).fv) :=
  by
  simpa only [nb067AlphaDummy294] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy291 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy291 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy291 f))).fv)
      0

theorem nb067_fresh_340 :
    (nb067AlphaDummy337) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy333)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy333)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy333))).fv) :=
  by
  simpa only [nb067AlphaDummy337] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy333)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy333)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy333))).fv)
      0

theorem nb067_fresh_341 (f : Var) :
    (nb067AlphaDummy338 f) ∉
      (((Wff.classMem (Class.cv (nb067AlphaDummy335 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy335 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy335 f))).fv) :=
  by
  simpa only [nb067AlphaDummy338] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb067AlphaDummy335 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy335 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy335 f))).fv)
      0

theorem nb067_fresh_342 :
    (nb067AlphaDummy277) ∉
      (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb067AlphaDummy277] using
    freshVar_not_mem (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪ ((synCvv)).fv)
      0

theorem nb067_fresh_343 :
    (nb067AlphaDummy278) ∉
      (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb067AlphaDummy278] using
    freshVar_not_mem (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪ ((synCvv)).fv)
      1

theorem nb067_distinct_344 : (nb067AlphaDummy277) ≠ (nb067AlphaDummy278) := by
  simpa only [nb067AlphaDummy277, nb067AlphaDummy278] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪ ((synCvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb067_fresh_345 (f : Var) :
    (nb067AlphaDummy279 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb067AlphaDummy279] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0

theorem nb067_fresh_346 (f : Var) :
    (nb067AlphaDummy280 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb067AlphaDummy280] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1

theorem nb067_distinct_347 (f : Var) :
    (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy280 f) := by
  simpa only [nb067AlphaDummy279, nb067AlphaDummy280] using
    (freshVar_injective (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb067_fresh_348 :
    (nb067AlphaDummy081) ∉
      (((synCcom (Class.cv (nb067AlphaDummy000))
            (synCcnv (Class.cv (nb067AlphaDummy000))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb067AlphaDummy081] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb067AlphaDummy000))
            (synCcnv (Class.cv (nb067AlphaDummy000))))).fv ∪ ((synCid)).fv)
      0

theorem nb067_fresh_349 (f : Var) :
    (nb067AlphaDummy082 f) ∉
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb067AlphaDummy082] using
    freshVar_not_mem
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0

theorem nb067_fresh_350 :
    (nb067AlphaDummy011) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
                (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCphi (Class.cv (nb067AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy007)
              (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
                (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCphi (Class.cv (nb067AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy007)
              (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_351 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy012 x y f) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy009 x y f)
              (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCphi (Class.cv (nb067AlphaDummy010 x y f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
                (Class.cv (nb067AlphaDummy004 x y f))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy012] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy009 x y f)
              (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCphi (Class.cv (nb067AlphaDummy010 x y f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
                (Class.cv (nb067AlphaDummy004 x y f))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_352 :
    (nb067AlphaDummy019) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCphi (Class.cv (nb067AlphaDummy016)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy019] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCphi (Class.cv (nb067AlphaDummy016)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_353 (x : Var) (y : Var) :
    (nb067AlphaDummy020 x y) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCphi (Class.cv (nb067AlphaDummy018 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy020] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCphi (Class.cv (nb067AlphaDummy018 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_354 :
    (nb067AlphaDummy095) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCphi (Class.cv (nb067AlphaDummy092)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy095] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCphi (Class.cv (nb067AlphaDummy092)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_355 (f : Var) :
    (nb067AlphaDummy096 f) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCphi (Class.cv (nb067AlphaDummy094 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy096] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCphi (Class.cv (nb067AlphaDummy094 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_356 :
    (nb067AlphaDummy131) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCphi (Class.cv (nb067AlphaDummy128)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy131] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCphi (Class.cv (nb067AlphaDummy128)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_357 (f : Var) :
    (nb067AlphaDummy132 f) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCphi (Class.cv (nb067AlphaDummy130 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy132] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCphi (Class.cv (nb067AlphaDummy130 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_358 :
    (nb067AlphaDummy173) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCphi (Class.cv (nb067AlphaDummy170)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy173] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCphi (Class.cv (nb067AlphaDummy170)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_359 (f : Var) :
    (nb067AlphaDummy174 f) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCphi (Class.cv (nb067AlphaDummy172 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy174] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCphi (Class.cv (nb067AlphaDummy172 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_360 :
    (nb067AlphaDummy209) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCphi (Class.cv (nb067AlphaDummy206)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy209] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCphi (Class.cv (nb067AlphaDummy206)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_361 (f : Var) :
    (nb067AlphaDummy210 f) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCphi (Class.cv (nb067AlphaDummy208 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy210] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCphi (Class.cv (nb067AlphaDummy208 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_362 :
    (nb067AlphaDummy245) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCphi (Class.cv (nb067AlphaDummy242)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy245] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCphi (Class.cv (nb067AlphaDummy242)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_363 (f : Var) :
    (nb067AlphaDummy246 f) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCphi (Class.cv (nb067AlphaDummy244 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy246] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCphi (Class.cv (nb067AlphaDummy244 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_364 :
    (nb067AlphaDummy285) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCphi (Class.cv (nb067AlphaDummy282)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy285] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCphi (Class.cv (nb067AlphaDummy282)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_365 (f : Var) :
    (nb067AlphaDummy286 f) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCphi (Class.cv (nb067AlphaDummy284 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy286] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCphi (Class.cv (nb067AlphaDummy284 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_366 :
    (nb067AlphaDummy329) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCphi (Class.cv (nb067AlphaDummy326)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy329] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy322))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCphi (Class.cv (nb067AlphaDummy326)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_367 (f : Var) :
    (nb067AlphaDummy330 f) ∉
      (((synCcompl (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCphi (Class.cv (nb067AlphaDummy328 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb067AlphaDummy330] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy324 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCphi (Class.cv (nb067AlphaDummy328 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb067_fresh_368 :
    (nb067AlphaDummy039) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy030)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy031)))).fv) :=
  by
  simpa only [nb067AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy030)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy031)))).fv)
      0

theorem nb067_fresh_369 (x : Var) (y : Var) :
    (nb067AlphaDummy040 x y) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy033 x y)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy034 x y)))).fv) :=
  by
  simpa only [nb067AlphaDummy040] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy033 x y)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy034 x y)))).fv)
      0

theorem nb067_fresh_370 :
    (nb067AlphaDummy067) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy058)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy059)))).fv) :=
  by
  simpa only [nb067AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy058)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy059)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
