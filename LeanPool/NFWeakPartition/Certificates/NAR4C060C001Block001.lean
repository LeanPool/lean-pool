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

/-! Certificates from `NAR4C060C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_000`. -/
@[expose]
noncomputable def nb060AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_001`. -/
@[expose]
noncomputable def nb060AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_002`. -/
@[expose]
noncomputable def nb060AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_003`. -/
@[expose]
noncomputable def nb060AlphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_004`. -/
@[expose]
noncomputable def nb060AlphaDummy004 : Var :=
  (freshVar ((∅ : Finset Var)) 4)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_005`. -/
@[expose]
noncomputable def nb060AlphaDummy005 : Var :=
  (freshVar
    (({(nb060AlphaDummy001)} : Finset Var) ∪ ({(nb060AlphaDummy000)} : Finset Var) ∪
      ((synWral (nb060AlphaDummy002) (Class.cv (nb060AlphaDummy000))
          (synWral (nb060AlphaDummy003) (Class.cv (nb060AlphaDummy000))
            (synWral (nb060AlphaDummy004) (Class.cv (nb060AlphaDummy000)) (Wff.imp
                (synWa (synWbr (Class.cv (nb060AlphaDummy002))
                    (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy003)))
                  (synWbr (Class.cv (nb060AlphaDummy003)) (Class.cv (nb060AlphaDummy001))
                    (Class.cv (nb060AlphaDummy004))))
                (synWbr (Class.cv (nb060AlphaDummy002)) (Class.cv (nb060AlphaDummy001))
                  (Class.cv (nb060AlphaDummy004)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_006`. -/
@[expose]
noncomputable def nb060AlphaDummy006 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
          (synWral y (Class.cv a) (synWral z (Class.cv a) (Wff.imp
                (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                  (synWbr (Class.cv y) (Class.cv r) (Class.cv z)))
                (synWbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_007`. -/
@[expose]
noncomputable def nb060AlphaDummy007 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_008`. -/
@[expose]
noncomputable def nb060AlphaDummy008 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_009`. -/
@[expose]
noncomputable def nb060AlphaDummy009 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_010`. -/
@[expose]
noncomputable def nb060AlphaDummy010 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_011`. -/
@[expose]
noncomputable def nb060AlphaDummy011 : Var :=
  (freshVar (((synCcompl (Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCphi (Class.cv (nb060AlphaDummy008)))))))).fv ∪ ((synCcompl
          (Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_012`. -/
@[expose]
noncomputable def nb060AlphaDummy012 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCphi (Class.cv (nb060AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
          (Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_013`. -/
@[expose]
noncomputable def nb060AlphaDummy013 : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy007)
          (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
            (Wff.classEq (Class.cv (nb060AlphaDummy007))
              (synCphi (Class.cv (nb060AlphaDummy008))))))).fv ∪
      ((Class.cab (nb060AlphaDummy007)
          (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
            (Wff.classEq (Class.cv (nb060AlphaDummy007))
              (synCphi (Class.cv (nb060AlphaDummy008))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_014`. -/
@[expose]
noncomputable def nb060AlphaDummy014 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy009 r a)
          (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
              (synCphi (Class.cv (nb060AlphaDummy010 r a))))))).fv ∪
      ((Class.cab (nb060AlphaDummy009 r a) (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
              (synCphi (Class.cv (nb060AlphaDummy010 r a))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_015`. -/
@[expose]
noncomputable def nb060AlphaDummy015 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy008))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_016`. -/
@[expose]
noncomputable def nb060AlphaDummy016 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy008))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_017`. -/
@[expose]
noncomputable def nb060AlphaDummy017 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy010 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_018`. -/
@[expose]
noncomputable def nb060AlphaDummy018 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy010 r a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_019`. -/
@[expose]
noncomputable def nb060AlphaDummy019 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060AlphaDummy015)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb060AlphaDummy015)) (synC1c))).fv ∪
      ((Class.cv (nb060AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_020`. -/
@[expose]
noncomputable def nb060AlphaDummy020 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060AlphaDummy017 r a)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb060AlphaDummy017 r a)) (synC1c))).fv ∪
      ((Class.cv (nb060AlphaDummy017 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_021`. -/
@[expose]
noncomputable def nb060AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_022`. -/
@[expose]
noncomputable def nb060AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_023`. -/
@[expose]
noncomputable def nb060AlphaDummy023 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_024`. -/
@[expose]
noncomputable def nb060AlphaDummy024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_025`. -/
@[expose]
noncomputable def nb060AlphaDummy025 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_026`. -/
@[expose]
noncomputable def nb060AlphaDummy026 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_027`. -/
@[expose]
noncomputable def nb060AlphaDummy027 : Var :=
  (freshVar (((synCnin (Class.cv (nb060AlphaDummy022))
          (Class.cv (nb060AlphaDummy023)))).fv ∪
      ((synCnin (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_028`. -/
@[expose]
noncomputable def nb060AlphaDummy028 (r : Var) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb060AlphaDummy025 r a))
          (Class.cv (nb060AlphaDummy026 r a)))).fv ∪
      ((synCnin (Class.cv (nb060AlphaDummy025 r a))
          (Class.cv (nb060AlphaDummy026 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_029`. -/
@[expose]
noncomputable def nb060AlphaDummy029 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_030`. -/
@[expose]
noncomputable def nb060AlphaDummy030 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
      ((Class.cv (nb060AlphaDummy026 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_031`. -/
@[expose]
noncomputable def nb060AlphaDummy031 : Var :=
  (freshVar (((synCcompl (Class.cv (nb060AlphaDummy022)))).fv ∪
      ((synCcompl (Class.cv (nb060AlphaDummy023)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_032`. -/
@[expose]
noncomputable def nb060AlphaDummy032 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb060AlphaDummy025 r a)))).fv ∪
      ((synCcompl (Class.cv (nb060AlphaDummy026 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_033`. -/
@[expose]
noncomputable def nb060AlphaDummy033 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_034`. -/
@[expose]
noncomputable def nb060AlphaDummy034 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
      ((Class.cv (nb060AlphaDummy025 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_035`. -/
@[expose]
noncomputable def nb060AlphaDummy035 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy023))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_036`. -/
@[expose]
noncomputable def nb060AlphaDummy036 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy026 r a))).fv ∪
      ((Class.cv (nb060AlphaDummy026 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_037`. -/
@[expose]
noncomputable def nb060AlphaDummy037 : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy007)
          (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
            (Wff.classEq (Class.cv (nb060AlphaDummy007))
              (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy007)
          (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
            (Wff.classEq (Class.cv (nb060AlphaDummy007))
              (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_038`. -/
@[expose]
noncomputable def nb060AlphaDummy038 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy009 r a)
          (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
              (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy009 r a)
          (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
              (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_039`. -/
@[expose]
noncomputable def nb060AlphaDummy039 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb060AlphaDummy008))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_040`. -/
@[expose]
noncomputable def nb060AlphaDummy040 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb060AlphaDummy010 r a))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_041`. -/
@[expose]
noncomputable def nb060AlphaDummy041 : Var :=
  (freshVar (((synCphi (Class.cv (nb060AlphaDummy008)))).fv ∪
      ((synCphi (Class.cv (nb060AlphaDummy008)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_042`. -/
@[expose]
noncomputable def nb060AlphaDummy042 (r : Var) (a : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb060AlphaDummy010 r a)))).fv ∪
      ((synCphi (Class.cv (nb060AlphaDummy010 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_043`. -/
@[expose]
noncomputable def nb060AlphaDummy043 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_044`. -/
@[expose]
noncomputable def nb060AlphaDummy044 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_045`. -/
@[expose]
noncomputable def nb060AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_046`. -/
@[expose]
noncomputable def nb060AlphaDummy046 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_047`. -/
@[expose]
noncomputable def nb060AlphaDummy047 : Var :=
  (freshVar (((synCcompl (Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCphi (Class.cv (nb060AlphaDummy044)))))))).fv ∪ ((synCcompl
          (Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_048`. -/
@[expose]
noncomputable def nb060AlphaDummy048 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCphi (Class.cv (nb060AlphaDummy046 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_049`. -/
@[expose]
noncomputable def nb060AlphaDummy049 : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy043)
          (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
            (Wff.classEq (Class.cv (nb060AlphaDummy043))
              (synCphi (Class.cv (nb060AlphaDummy044))))))).fv ∪
      ((Class.cab (nb060AlphaDummy043)
          (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
            (Wff.classEq (Class.cv (nb060AlphaDummy043))
              (synCphi (Class.cv (nb060AlphaDummy044))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_050`. -/
@[expose]
noncomputable def nb060AlphaDummy050 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy045 x y)
          (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
              (synCphi (Class.cv (nb060AlphaDummy046 x y))))))).fv ∪
      ((Class.cab (nb060AlphaDummy045 x y) (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
              (synCphi (Class.cv (nb060AlphaDummy046 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_051`. -/
@[expose]
noncomputable def nb060AlphaDummy051 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy044))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_052`. -/
@[expose]
noncomputable def nb060AlphaDummy052 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy044))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_053`. -/
@[expose]
noncomputable def nb060AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy046 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_054`. -/
@[expose]
noncomputable def nb060AlphaDummy054 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy046 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_055`. -/
@[expose]
noncomputable def nb060AlphaDummy055 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060AlphaDummy051)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb060AlphaDummy051)) (synC1c))).fv ∪
      ((Class.cv (nb060AlphaDummy051))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_056`. -/
@[expose]
noncomputable def nb060AlphaDummy056 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060AlphaDummy053 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb060AlphaDummy053 x y)) (synC1c))).fv ∪
      ((Class.cv (nb060AlphaDummy053 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_057`. -/
@[expose]
noncomputable def nb060AlphaDummy057 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_058`. -/
@[expose]
noncomputable def nb060AlphaDummy058 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_059`. -/
@[expose]
noncomputable def nb060AlphaDummy059 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_060`. -/
@[expose]
noncomputable def nb060AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_061`. -/
@[expose]
noncomputable def nb060AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_062`. -/
@[expose]
noncomputable def nb060AlphaDummy062 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_063`. -/
@[expose]
noncomputable def nb060AlphaDummy063 : Var :=
  (freshVar (((synCnin (Class.cv (nb060AlphaDummy058))
          (Class.cv (nb060AlphaDummy059)))).fv ∪
      ((synCnin (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_064`. -/
@[expose]
noncomputable def nb060AlphaDummy064 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb060AlphaDummy061 x y))
          (Class.cv (nb060AlphaDummy062 x y)))).fv ∪
      ((synCnin (Class.cv (nb060AlphaDummy061 x y))
          (Class.cv (nb060AlphaDummy062 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_065`. -/
@[expose]
noncomputable def nb060AlphaDummy065 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_066`. -/
@[expose]
noncomputable def nb060AlphaDummy066 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb060AlphaDummy062 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_067`. -/
@[expose]
noncomputable def nb060AlphaDummy067 : Var :=
  (freshVar (((synCcompl (Class.cv (nb060AlphaDummy058)))).fv ∪
      ((synCcompl (Class.cv (nb060AlphaDummy059)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_068`. -/
@[expose]
noncomputable def nb060AlphaDummy068 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb060AlphaDummy061 x y)))).fv ∪
      ((synCcompl (Class.cv (nb060AlphaDummy062 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_069`. -/
@[expose]
noncomputable def nb060AlphaDummy069 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_070`. -/
@[expose]
noncomputable def nb060AlphaDummy070 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb060AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_071`. -/
@[expose]
noncomputable def nb060AlphaDummy071 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy059))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_072`. -/
@[expose]
noncomputable def nb060AlphaDummy072 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy062 x y))).fv ∪
      ((Class.cv (nb060AlphaDummy062 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_073`. -/
@[expose]
noncomputable def nb060AlphaDummy073 : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy043)
          (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
            (Wff.classEq (Class.cv (nb060AlphaDummy043))
              (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy043)
          (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
            (Wff.classEq (Class.cv (nb060AlphaDummy043))
              (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_074`. -/
@[expose]
noncomputable def nb060AlphaDummy074 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy045 x y)
          (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
              (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy045 x y)
          (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
              (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_075`. -/
@[expose]
noncomputable def nb060AlphaDummy075 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb060AlphaDummy044))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_076`. -/
@[expose]
noncomputable def nb060AlphaDummy076 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb060AlphaDummy046 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_077`. -/
@[expose]
noncomputable def nb060AlphaDummy077 : Var :=
  (freshVar (((synCphi (Class.cv (nb060AlphaDummy044)))).fv ∪
      ((synCphi (Class.cv (nb060AlphaDummy044)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_078`. -/
@[expose]
noncomputable def nb060AlphaDummy078 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb060AlphaDummy046 x y)))).fv ∪
      ((synCphi (Class.cv (nb060AlphaDummy046 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_079`. -/
@[expose]
noncomputable def nb060AlphaDummy079 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_080`. -/
@[expose]
noncomputable def nb060AlphaDummy080 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_081`. -/
@[expose]
noncomputable def nb060AlphaDummy081 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_082`. -/
@[expose]
noncomputable def nb060AlphaDummy082 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_083`. -/
@[expose]
noncomputable def nb060AlphaDummy083 : Var :=
  (freshVar (((synCcompl (Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCphi (Class.cv (nb060AlphaDummy080)))))))).fv ∪ ((synCcompl
          (Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_084`. -/
@[expose]
noncomputable def nb060AlphaDummy084 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCphi (Class.cv (nb060AlphaDummy082 y z)))))))).fv ∪ ((synCcompl
          (Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_085`. -/
@[expose]
noncomputable def nb060AlphaDummy085 : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy079)
          (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
            (Wff.classEq (Class.cv (nb060AlphaDummy079))
              (synCphi (Class.cv (nb060AlphaDummy080))))))).fv ∪
      ((Class.cab (nb060AlphaDummy079)
          (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
            (Wff.classEq (Class.cv (nb060AlphaDummy079))
              (synCphi (Class.cv (nb060AlphaDummy080))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_086`. -/
@[expose]
noncomputable def nb060AlphaDummy086 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy081 y z)
          (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
            (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
              (synCphi (Class.cv (nb060AlphaDummy082 y z))))))).fv ∪
      ((Class.cab (nb060AlphaDummy081 y z) (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
            (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
              (synCphi (Class.cv (nb060AlphaDummy082 y z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_087`. -/
@[expose]
noncomputable def nb060AlphaDummy087 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy080))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_088`. -/
@[expose]
noncomputable def nb060AlphaDummy088 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy080))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_089`. -/
@[expose]
noncomputable def nb060AlphaDummy089 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy082 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_090`. -/
@[expose]
noncomputable def nb060AlphaDummy090 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy082 y z))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_091`. -/
@[expose]
noncomputable def nb060AlphaDummy091 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060AlphaDummy087)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb060AlphaDummy087)) (synC1c))).fv ∪
      ((Class.cv (nb060AlphaDummy087))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_092`. -/
@[expose]
noncomputable def nb060AlphaDummy092 (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060AlphaDummy089 y z)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb060AlphaDummy089 y z)) (synC1c))).fv ∪
      ((Class.cv (nb060AlphaDummy089 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_093`. -/
@[expose]
noncomputable def nb060AlphaDummy093 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_094`. -/
@[expose]
noncomputable def nb060AlphaDummy094 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_095`. -/
@[expose]
noncomputable def nb060AlphaDummy095 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_096`. -/
@[expose]
noncomputable def nb060AlphaDummy096 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_097`. -/
@[expose]
noncomputable def nb060AlphaDummy097 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_098`. -/
@[expose]
noncomputable def nb060AlphaDummy098 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_099`. -/
@[expose]
noncomputable def nb060AlphaDummy099 : Var :=
  (freshVar (((synCnin (Class.cv (nb060AlphaDummy094))
          (Class.cv (nb060AlphaDummy095)))).fv ∪
      ((synCnin (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_100`. -/
@[expose]
noncomputable def nb060AlphaDummy100 (y : Var) (z : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb060AlphaDummy097 y z))
          (Class.cv (nb060AlphaDummy098 y z)))).fv ∪
      ((synCnin (Class.cv (nb060AlphaDummy097 y z))
          (Class.cv (nb060AlphaDummy098 y z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_101`. -/
@[expose]
noncomputable def nb060AlphaDummy101 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_102`. -/
@[expose]
noncomputable def nb060AlphaDummy102 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
      ((Class.cv (nb060AlphaDummy098 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_103`. -/
@[expose]
noncomputable def nb060AlphaDummy103 : Var :=
  (freshVar (((synCcompl (Class.cv (nb060AlphaDummy094)))).fv ∪
      ((synCcompl (Class.cv (nb060AlphaDummy095)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_104`. -/
@[expose]
noncomputable def nb060AlphaDummy104 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb060AlphaDummy097 y z)))).fv ∪
      ((synCcompl (Class.cv (nb060AlphaDummy098 y z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_105`. -/
@[expose]
noncomputable def nb060AlphaDummy105 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy094))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_106`. -/
@[expose]
noncomputable def nb060AlphaDummy106 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
      ((Class.cv (nb060AlphaDummy097 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_107`. -/
@[expose]
noncomputable def nb060AlphaDummy107 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy095))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_108`. -/
@[expose]
noncomputable def nb060AlphaDummy108 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy098 y z))).fv ∪
      ((Class.cv (nb060AlphaDummy098 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_109`. -/
@[expose]
noncomputable def nb060AlphaDummy109 : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy079)
          (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
            (Wff.classEq (Class.cv (nb060AlphaDummy079))
              (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy079)
          (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
            (Wff.classEq (Class.cv (nb060AlphaDummy079))
              (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_110`. -/
@[expose]
noncomputable def nb060AlphaDummy110 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy081 y z)
          (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
              (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy081 y z)
          (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
              (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_111`. -/
@[expose]
noncomputable def nb060AlphaDummy111 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb060AlphaDummy080))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_112`. -/
@[expose]
noncomputable def nb060AlphaDummy112 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb060AlphaDummy082 y z))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_113`. -/
@[expose]
noncomputable def nb060AlphaDummy113 : Var :=
  (freshVar (((synCphi (Class.cv (nb060AlphaDummy080)))).fv ∪
      ((synCphi (Class.cv (nb060AlphaDummy080)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_114`. -/
@[expose]
noncomputable def nb060AlphaDummy114 (y : Var) (z : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb060AlphaDummy082 y z)))).fv ∪
      ((synCphi (Class.cv (nb060AlphaDummy082 y z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_115`. -/
@[expose]
noncomputable def nb060AlphaDummy115 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_116`. -/
@[expose]
noncomputable def nb060AlphaDummy116 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_117`. -/
@[expose]
noncomputable def nb060AlphaDummy117 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_118`. -/
@[expose]
noncomputable def nb060AlphaDummy118 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_119`. -/
@[expose]
noncomputable def nb060AlphaDummy119 : Var :=
  (freshVar (((synCcompl (Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCphi (Class.cv (nb060AlphaDummy116)))))))).fv ∪ ((synCcompl
          (Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_120`. -/
@[expose]
noncomputable def nb060AlphaDummy120 (x : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCphi (Class.cv (nb060AlphaDummy118 x z)))))))).fv ∪ ((synCcompl
          (Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_121`. -/
@[expose]
noncomputable def nb060AlphaDummy121 : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy115)
          (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
            (Wff.classEq (Class.cv (nb060AlphaDummy115))
              (synCphi (Class.cv (nb060AlphaDummy116))))))).fv ∪
      ((Class.cab (nb060AlphaDummy115)
          (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
            (Wff.classEq (Class.cv (nb060AlphaDummy115))
              (synCphi (Class.cv (nb060AlphaDummy116))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_122`. -/
@[expose]
noncomputable def nb060AlphaDummy122 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy117 x z)
          (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
            (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
              (synCphi (Class.cv (nb060AlphaDummy118 x z))))))).fv ∪
      ((Class.cab (nb060AlphaDummy117 x z) (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
            (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
              (synCphi (Class.cv (nb060AlphaDummy118 x z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_123`. -/
@[expose]
noncomputable def nb060AlphaDummy123 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy116))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_124`. -/
@[expose]
noncomputable def nb060AlphaDummy124 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy116))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_125`. -/
@[expose]
noncomputable def nb060AlphaDummy125 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy118 x z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_126`. -/
@[expose]
noncomputable def nb060AlphaDummy126 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy118 x z))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_127`. -/
@[expose]
noncomputable def nb060AlphaDummy127 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060AlphaDummy123)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb060AlphaDummy123)) (synC1c))).fv ∪
      ((Class.cv (nb060AlphaDummy123))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_128`. -/
@[expose]
noncomputable def nb060AlphaDummy128 (x : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb060AlphaDummy125 x z)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb060AlphaDummy125 x z)) (synC1c))).fv ∪
      ((Class.cv (nb060AlphaDummy125 x z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_129`. -/
@[expose]
noncomputable def nb060AlphaDummy129 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_130`. -/
@[expose]
noncomputable def nb060AlphaDummy130 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_131`. -/
@[expose]
noncomputable def nb060AlphaDummy131 : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_132`. -/
@[expose]
noncomputable def nb060AlphaDummy132 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_133`. -/
@[expose]
noncomputable def nb060AlphaDummy133 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_134`. -/
@[expose]
noncomputable def nb060AlphaDummy134 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_135`. -/
@[expose]
noncomputable def nb060AlphaDummy135 : Var :=
  (freshVar (((synCnin (Class.cv (nb060AlphaDummy130))
          (Class.cv (nb060AlphaDummy131)))).fv ∪
      ((synCnin (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_136`. -/
@[expose]
noncomputable def nb060AlphaDummy136 (x : Var) (z : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb060AlphaDummy133 x z))
          (Class.cv (nb060AlphaDummy134 x z)))).fv ∪
      ((synCnin (Class.cv (nb060AlphaDummy133 x z))
          (Class.cv (nb060AlphaDummy134 x z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_137`. -/
@[expose]
noncomputable def nb060AlphaDummy137 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_138`. -/
@[expose]
noncomputable def nb060AlphaDummy138 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
      ((Class.cv (nb060AlphaDummy134 x z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_139`. -/
@[expose]
noncomputable def nb060AlphaDummy139 : Var :=
  (freshVar (((synCcompl (Class.cv (nb060AlphaDummy130)))).fv ∪
      ((synCcompl (Class.cv (nb060AlphaDummy131)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_140`. -/
@[expose]
noncomputable def nb060AlphaDummy140 (x : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb060AlphaDummy133 x z)))).fv ∪
      ((synCcompl (Class.cv (nb060AlphaDummy134 x z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_141`. -/
@[expose]
noncomputable def nb060AlphaDummy141 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy130))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_142`. -/
@[expose]
noncomputable def nb060AlphaDummy142 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
      ((Class.cv (nb060AlphaDummy133 x z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_143`. -/
@[expose]
noncomputable def nb060AlphaDummy143 : Var :=
  (freshVar
    (((Class.cv (nb060AlphaDummy131))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_144`. -/
@[expose]
noncomputable def nb060AlphaDummy144 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb060AlphaDummy134 x z))).fv ∪
      ((Class.cv (nb060AlphaDummy134 x z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_145`. -/
@[expose]
noncomputable def nb060AlphaDummy145 : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy115)
          (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
            (Wff.classEq (Class.cv (nb060AlphaDummy115))
              (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy115)
          (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
            (Wff.classEq (Class.cv (nb060AlphaDummy115))
              (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_146`. -/
@[expose]
noncomputable def nb060AlphaDummy146 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb060AlphaDummy117 x z)
          (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
            (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
              (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy117 x z)
          (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
            (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
              (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_147`. -/
@[expose]
noncomputable def nb060AlphaDummy147 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb060AlphaDummy116))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_148`. -/
@[expose]
noncomputable def nb060AlphaDummy148 (x : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb060AlphaDummy118 x z))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_149`. -/
@[expose]
noncomputable def nb060AlphaDummy149 : Var :=
  (freshVar (((synCphi (Class.cv (nb060AlphaDummy116)))).fv ∪
      ((synCphi (Class.cv (nb060AlphaDummy116)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb060_alpha_dummy_150`. -/
@[expose]
noncomputable def nb060AlphaDummy150 (x : Var) (z : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb060AlphaDummy118 x z)))).fv ∪
      ((synCphi (Class.cv (nb060AlphaDummy118 x z)))).fv) 0)

theorem nb060_fresh_000 :
    (nb060AlphaDummy037) ∉
      (((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb060AlphaDummy037] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb060_fresh_001 :
    (nb060AlphaDummy013) ∉
      (((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCphi (Class.cv (nb060AlphaDummy008))))))).fv ∪
        ((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCphi (Class.cv (nb060AlphaDummy008))))))).fv) :=
  by
  simpa only [nb060AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCphi (Class.cv (nb060AlphaDummy008))))))).fv ∪
        ((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCphi (Class.cv (nb060AlphaDummy008))))))).fv)
      0

theorem nb060_fresh_002 (r : Var) (a : Var) :
    (nb060AlphaDummy038 r a) ∉
      (((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb060AlphaDummy038] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb060_fresh_003 (r : Var) (a : Var) :
    (nb060AlphaDummy014 r a) ∉
      (((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCphi (Class.cv (nb060AlphaDummy010 r a))))))).fv ∪
        ((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCphi (Class.cv (nb060AlphaDummy010 r a))))))).fv) :=
  by
  simpa only [nb060AlphaDummy014] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCphi (Class.cv (nb060AlphaDummy010 r a))))))).fv ∪
        ((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCphi (Class.cv (nb060AlphaDummy010 r a))))))).fv)
      0

theorem nb060_fresh_004 :
    (nb060AlphaDummy049) ∉
      (((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCphi (Class.cv (nb060AlphaDummy044))))))).fv ∪
        ((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCphi (Class.cv (nb060AlphaDummy044))))))).fv) :=
  by
  simpa only [nb060AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCphi (Class.cv (nb060AlphaDummy044))))))).fv ∪
        ((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCphi (Class.cv (nb060AlphaDummy044))))))).fv)
      0

theorem nb060_fresh_005 :
    (nb060AlphaDummy073) ∉
      (((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb060AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb060_fresh_006 (x : Var) (y : Var) :
    (nb060AlphaDummy050 x y) ∉
      (((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCphi (Class.cv (nb060AlphaDummy046 x y))))))).fv ∪
        ((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCphi (Class.cv (nb060AlphaDummy046 x y))))))).fv) :=
  by
  simpa only [nb060AlphaDummy050] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCphi (Class.cv (nb060AlphaDummy046 x y))))))).fv ∪
        ((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCphi (Class.cv (nb060AlphaDummy046 x y))))))).fv)
      0

theorem nb060_fresh_007 (x : Var) (y : Var) :
    (nb060AlphaDummy074 x y) ∉
      (((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb060AlphaDummy074] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb060_fresh_008 :
    (nb060AlphaDummy085) ∉
      (((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCphi (Class.cv (nb060AlphaDummy080))))))).fv ∪
        ((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCphi (Class.cv (nb060AlphaDummy080))))))).fv) :=
  by
  simpa only [nb060AlphaDummy085] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCphi (Class.cv (nb060AlphaDummy080))))))).fv ∪
        ((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCphi (Class.cv (nb060AlphaDummy080))))))).fv)
      0

theorem nb060_fresh_009 :
    (nb060AlphaDummy109) ∉
      (((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb060AlphaDummy109] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb060_fresh_010 (y : Var) (z : Var) :
    (nb060AlphaDummy086 y z) ∉
      (((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCphi (Class.cv (nb060AlphaDummy082 y z))))))).fv ∪
        ((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCphi (Class.cv (nb060AlphaDummy082 y z))))))).fv) :=
  by
  simpa only [nb060AlphaDummy086] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCphi (Class.cv (nb060AlphaDummy082 y z))))))).fv ∪
        ((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCphi (Class.cv (nb060AlphaDummy082 y z))))))).fv)
      0

theorem nb060_fresh_011 (y : Var) (z : Var) :
    (nb060AlphaDummy110 y z) ∉
      (((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb060AlphaDummy110] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb060_fresh_012 :
    (nb060AlphaDummy121) ∉
      (((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCphi (Class.cv (nb060AlphaDummy116))))))).fv ∪
        ((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCphi (Class.cv (nb060AlphaDummy116))))))).fv) :=
  by
  simpa only [nb060AlphaDummy121] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCphi (Class.cv (nb060AlphaDummy116))))))).fv ∪
        ((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCphi (Class.cv (nb060AlphaDummy116))))))).fv)
      0

theorem nb060_fresh_013 :
    (nb060AlphaDummy145) ∉
      (((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb060AlphaDummy145] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb060_fresh_014 (x : Var) (z : Var) :
    (nb060AlphaDummy122 x z) ∉
      (((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCphi (Class.cv (nb060AlphaDummy118 x z))))))).fv ∪
        ((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCphi (Class.cv (nb060AlphaDummy118 x z))))))).fv) :=
  by
  simpa only [nb060AlphaDummy122] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCphi (Class.cv (nb060AlphaDummy118 x z))))))).fv ∪
        ((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCphi (Class.cv (nb060AlphaDummy118 x z))))))).fv)
      0

theorem nb060_fresh_015 (x : Var) (z : Var) :
    (nb060AlphaDummy146 x z) ∉
      (((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb060AlphaDummy146] using
    freshVar_not_mem
      (((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb060_fresh_016 :
    (nb060AlphaDummy007) ∉
      (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv) :=
  by
  simpa only [nb060AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv)
      0

theorem nb060_fresh_017 :
    (nb060AlphaDummy008) ∉
      (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv) :=
  by
  simpa only [nb060AlphaDummy008] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv)
      1

theorem nb060_distinct_018 : (nb060AlphaDummy007) ≠ (nb060AlphaDummy008) := by
  simpa only [nb060AlphaDummy007, nb060AlphaDummy008] using
    (freshVar_injective
      (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_fresh_019 :
    (nb060AlphaDummy043) ∉
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv) :=
  by
  simpa only [nb060AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv)
      0

theorem nb060_fresh_020 :
    (nb060AlphaDummy044) ∉
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv) :=
  by
  simpa only [nb060AlphaDummy044] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv)
      1

theorem nb060_distinct_021 : (nb060AlphaDummy043) ≠ (nb060AlphaDummy044) := by
  simpa only [nb060AlphaDummy043, nb060AlphaDummy044] using
    (freshVar_injective
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_fresh_022 :
    (nb060AlphaDummy115) ∉
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) :=
  by
  simpa only [nb060AlphaDummy115] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv)
      0

theorem nb060_fresh_023 :
    (nb060AlphaDummy116) ∉
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) :=
  by
  simpa only [nb060AlphaDummy116] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv)
      1

theorem nb060_distinct_024 : (nb060AlphaDummy115) ≠ (nb060AlphaDummy116) := by
  simpa only [nb060AlphaDummy115, nb060AlphaDummy116] using
    (freshVar_injective
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_fresh_025 :
    (nb060AlphaDummy079) ∉
      (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) :=
  by
  simpa only [nb060AlphaDummy079] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv)
      0

theorem nb060_fresh_026 :
    (nb060AlphaDummy080) ∉
      (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) :=
  by
  simpa only [nb060AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv)
      1

theorem nb060_distinct_027 : (nb060AlphaDummy079) ≠ (nb060AlphaDummy080) := by
  simpa only [nb060AlphaDummy079, nb060AlphaDummy080] using
    (freshVar_injective
      (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_fresh_028 :
    (nb060AlphaDummy015) ∉ (((Class.cv (nb060AlphaDummy008))).fv) := by
  simpa only [nb060AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy008))).fv) 0

theorem nb060_fresh_029 :
    (nb060AlphaDummy016) ∉ (((Class.cv (nb060AlphaDummy008))).fv) := by
  simpa only [nb060AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy008))).fv) 1

theorem nb060_distinct_030 : (nb060AlphaDummy015) ≠ (nb060AlphaDummy016) := by
  simpa only [nb060AlphaDummy015, nb060AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy008))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_031 (r : Var) (a : Var) :
    (nb060AlphaDummy017 r a) ∉ (((Class.cv (nb060AlphaDummy010 r a))).fv) := by
  simpa only [nb060AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy010 r a))).fv) 0

theorem nb060_fresh_032 (r : Var) (a : Var) :
    (nb060AlphaDummy018 r a) ∉ (((Class.cv (nb060AlphaDummy010 r a))).fv) := by
  simpa only [nb060AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy010 r a))).fv) 1

theorem nb060_distinct_033 (r : Var) (a : Var) :
    (nb060AlphaDummy017 r a) ≠ (nb060AlphaDummy018 r a) := by
  simpa only [nb060AlphaDummy017, nb060AlphaDummy018] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy010 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb060_fresh_034 :
    (nb060AlphaDummy021) ∉
      (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) 0

theorem nb060_fresh_035 :
    (nb060AlphaDummy022) ∉
      (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) 1

theorem nb060_fresh_036 :
    (nb060AlphaDummy023) ∉
      (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) 2

theorem nb060_distinct_037 : (nb060AlphaDummy021) ≠ (nb060AlphaDummy022) := by
  simpa only [nb060AlphaDummy021, nb060AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb060_distinct_038 : (nb060AlphaDummy021) ≠ (nb060AlphaDummy023) := by
  simpa only [nb060AlphaDummy021, nb060AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb060_distinct_039 : (nb060AlphaDummy022) ≠ (nb060AlphaDummy023) := by
  simpa only [nb060AlphaDummy022, nb060AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb060_fresh_040 (r : Var) (a : Var) :
    (nb060AlphaDummy024 r a) ∉
      (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 0

theorem nb060_fresh_041 (r : Var) (a : Var) :
    (nb060AlphaDummy025 r a) ∉
      (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 1

theorem nb060_fresh_042 (r : Var) (a : Var) :
    (nb060AlphaDummy026 r a) ∉
      (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 2

theorem nb060_distinct_043 (r : Var) (a : Var) :
    (nb060AlphaDummy024 r a) ≠ (nb060AlphaDummy025 r a) := by
  simpa only [nb060AlphaDummy024, nb060AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_distinct_044 (r : Var) (a : Var) :
    (nb060AlphaDummy024 r a) ≠ (nb060AlphaDummy026 r a) := by
  simpa only [nb060AlphaDummy024, nb060AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb060_distinct_045 (r : Var) (a : Var) :
    (nb060AlphaDummy025 r a) ≠ (nb060AlphaDummy026 r a) := by
  simpa only [nb060AlphaDummy025, nb060AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb060_fresh_046 :
    (nb060AlphaDummy033) ∉
      (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy022))).fv) :=
  by
  simpa only [nb060AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy022))).fv)
      0

theorem nb060_fresh_047 :
    (nb060AlphaDummy029) ∉
      (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv) :=
  by
  simpa only [nb060AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv)
      0

theorem nb060_fresh_048 :
    (nb060AlphaDummy035) ∉
      (((Class.cv (nb060AlphaDummy023))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv) :=
  by
  simpa only [nb060AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy023))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv)
      0

theorem nb060_fresh_049 (r : Var) (a : Var) :
    (nb060AlphaDummy034 r a) ∉
      (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy025 r a))).fv) :=
  by
  simpa only [nb060AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy025 r a))).fv)
      0

theorem nb060_fresh_050 (r : Var) (a : Var) :
    (nb060AlphaDummy030 r a) ∉
      (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy026 r a))).fv) :=
  by
  simpa only [nb060AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy026 r a))).fv)
      0

theorem nb060_fresh_051 (r : Var) (a : Var) :
    (nb060AlphaDummy036 r a) ∉
      (((Class.cv (nb060AlphaDummy026 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy026 r a))).fv) :=
  by
  simpa only [nb060AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy026 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy026 r a))).fv)
      0

theorem nb060_fresh_052 :
    (nb060AlphaDummy051) ∉ (((Class.cv (nb060AlphaDummy044))).fv) := by
  simpa only [nb060AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy044))).fv) 0

theorem nb060_fresh_053 :
    (nb060AlphaDummy052) ∉ (((Class.cv (nb060AlphaDummy044))).fv) := by
  simpa only [nb060AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy044))).fv) 1

theorem nb060_distinct_054 : (nb060AlphaDummy051) ≠ (nb060AlphaDummy052) := by
  simpa only [nb060AlphaDummy051, nb060AlphaDummy052] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy044))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_055 (x : Var) (y : Var) :
    (nb060AlphaDummy053 x y) ∉ (((Class.cv (nb060AlphaDummy046 x y))).fv) := by
  simpa only [nb060AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy046 x y))).fv) 0

theorem nb060_fresh_056 (x : Var) (y : Var) :
    (nb060AlphaDummy054 x y) ∉ (((Class.cv (nb060AlphaDummy046 x y))).fv) := by
  simpa only [nb060AlphaDummy054] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy046 x y))).fv) 1

theorem nb060_distinct_057 (x : Var) (y : Var) :
    (nb060AlphaDummy053 x y) ≠ (nb060AlphaDummy054 x y) := by
  simpa only [nb060AlphaDummy053, nb060AlphaDummy054] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy046 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb060_fresh_058 :
    (nb060AlphaDummy057) ∉
      (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) 0

theorem nb060_fresh_059 :
    (nb060AlphaDummy058) ∉
      (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) 1

theorem nb060_fresh_060 :
    (nb060AlphaDummy059) ∉
      (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) 2

theorem nb060_distinct_061 : (nb060AlphaDummy057) ≠ (nb060AlphaDummy058) := by
  simpa only [nb060AlphaDummy057, nb060AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb060_distinct_062 : (nb060AlphaDummy057) ≠ (nb060AlphaDummy059) := by
  simpa only [nb060AlphaDummy057, nb060AlphaDummy059] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb060_distinct_063 : (nb060AlphaDummy058) ≠ (nb060AlphaDummy059) := by
  simpa only [nb060AlphaDummy058, nb060AlphaDummy059] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb060_fresh_064 (x : Var) (y : Var) :
    (nb060AlphaDummy060 x y) ∉
      (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb060_fresh_065 (x : Var) (y : Var) :
    (nb060AlphaDummy061 x y) ∉
      (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb060_fresh_066 (x : Var) (y : Var) :
    (nb060AlphaDummy062 x y) ∉
      (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb060_distinct_067 (x : Var) (y : Var) :
    (nb060AlphaDummy060 x y) ≠ (nb060AlphaDummy061 x y) := by
  simpa only [nb060AlphaDummy060, nb060AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_distinct_068 (x : Var) (y : Var) :
    (nb060AlphaDummy060 x y) ≠ (nb060AlphaDummy062 x y) := by
  simpa only [nb060AlphaDummy060, nb060AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb060_distinct_069 (x : Var) (y : Var) :
    (nb060AlphaDummy061 x y) ≠ (nb060AlphaDummy062 x y) := by
  simpa only [nb060AlphaDummy061, nb060AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb060_fresh_070 :
    (nb060AlphaDummy069) ∉
      (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy058))).fv) :=
  by
  simpa only [nb060AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy058))).fv)
      0

theorem nb060_fresh_071 :
    (nb060AlphaDummy065) ∉
      (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv) :=
  by
  simpa only [nb060AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv)
      0

theorem nb060_fresh_072 :
    (nb060AlphaDummy071) ∉
      (((Class.cv (nb060AlphaDummy059))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv) :=
  by
  simpa only [nb060AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy059))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv)
      0

theorem nb060_fresh_073 (x : Var) (y : Var) :
    (nb060AlphaDummy070 x y) ∉
      (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb060AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy061 x y))).fv)
      0

theorem nb060_fresh_074 (x : Var) (y : Var) :
    (nb060AlphaDummy066 x y) ∉
      (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy062 x y))).fv) :=
  by
  simpa only [nb060AlphaDummy066] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy062 x y))).fv)
      0

theorem nb060_fresh_075 (x : Var) (y : Var) :
    (nb060AlphaDummy072 x y) ∉
      (((Class.cv (nb060AlphaDummy062 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy062 x y))).fv) :=
  by
  simpa only [nb060AlphaDummy072] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy062 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy062 x y))).fv)
      0

theorem nb060_fresh_076 :
    (nb060AlphaDummy087) ∉ (((Class.cv (nb060AlphaDummy080))).fv) := by
  simpa only [nb060AlphaDummy087] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy080))).fv) 0

theorem nb060_fresh_077 :
    (nb060AlphaDummy088) ∉ (((Class.cv (nb060AlphaDummy080))).fv) := by
  simpa only [nb060AlphaDummy088] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy080))).fv) 1

theorem nb060_distinct_078 : (nb060AlphaDummy087) ≠ (nb060AlphaDummy088) := by
  simpa only [nb060AlphaDummy087, nb060AlphaDummy088] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy080))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_079 (y : Var) (z : Var) :
    (nb060AlphaDummy089 y z) ∉ (((Class.cv (nb060AlphaDummy082 y z))).fv) := by
  simpa only [nb060AlphaDummy089] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy082 y z))).fv) 0

theorem nb060_fresh_080 (y : Var) (z : Var) :
    (nb060AlphaDummy090 y z) ∉ (((Class.cv (nb060AlphaDummy082 y z))).fv) := by
  simpa only [nb060AlphaDummy090] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy082 y z))).fv) 1

theorem nb060_distinct_081 (y : Var) (z : Var) :
    (nb060AlphaDummy089 y z) ≠ (nb060AlphaDummy090 y z) := by
  simpa only [nb060AlphaDummy089, nb060AlphaDummy090] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy082 y z))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb060_fresh_082 :
    (nb060AlphaDummy093) ∉
      (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy093] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) 0

theorem nb060_fresh_083 :
    (nb060AlphaDummy094) ∉
      (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy094] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) 1

theorem nb060_fresh_084 :
    (nb060AlphaDummy095) ∉
      (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy095] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) 2

theorem nb060_distinct_085 : (nb060AlphaDummy093) ≠ (nb060AlphaDummy094) := by
  simpa only [nb060AlphaDummy093, nb060AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb060_distinct_086 : (nb060AlphaDummy093) ≠ (nb060AlphaDummy095) := by
  simpa only [nb060AlphaDummy093, nb060AlphaDummy095] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb060_distinct_087 : (nb060AlphaDummy094) ≠ (nb060AlphaDummy095) := by
  simpa only [nb060AlphaDummy094, nb060AlphaDummy095] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb060_fresh_088 (y : Var) (z : Var) :
    (nb060AlphaDummy096 y z) ∉
      (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) 0

theorem nb060_fresh_089 (y : Var) (z : Var) :
    (nb060AlphaDummy097 y z) ∉
      (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) 1

theorem nb060_fresh_090 (y : Var) (z : Var) :
    (nb060AlphaDummy098 y z) ∉
      (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy098] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) 2

theorem nb060_distinct_091 (y : Var) (z : Var) :
    (nb060AlphaDummy096 y z) ≠ (nb060AlphaDummy097 y z) := by
  simpa only [nb060AlphaDummy096, nb060AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_distinct_092 (y : Var) (z : Var) :
    (nb060AlphaDummy096 y z) ≠ (nb060AlphaDummy098 y z) := by
  simpa only [nb060AlphaDummy096, nb060AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb060_distinct_093 (y : Var) (z : Var) :
    (nb060AlphaDummy097 y z) ≠ (nb060AlphaDummy098 y z) := by
  simpa only [nb060AlphaDummy097, nb060AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb060_fresh_094 :
    (nb060AlphaDummy105) ∉
      (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy094))).fv) :=
  by
  simpa only [nb060AlphaDummy105] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy094))).fv)
      0

theorem nb060_fresh_095 :
    (nb060AlphaDummy101) ∉
      (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv) :=
  by
  simpa only [nb060AlphaDummy101] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv)
      0

theorem nb060_fresh_096 :
    (nb060AlphaDummy107) ∉
      (((Class.cv (nb060AlphaDummy095))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv) :=
  by
  simpa only [nb060AlphaDummy107] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy095))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv)
      0

theorem nb060_fresh_097 (y : Var) (z : Var) :
    (nb060AlphaDummy106 y z) ∉
      (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy097 y z))).fv) :=
  by
  simpa only [nb060AlphaDummy106] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy097 y z))).fv)
      0

theorem nb060_fresh_098 (y : Var) (z : Var) :
    (nb060AlphaDummy102 y z) ∉
      (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy098 y z))).fv) :=
  by
  simpa only [nb060AlphaDummy102] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy098 y z))).fv)
      0

theorem nb060_fresh_099 (y : Var) (z : Var) :
    (nb060AlphaDummy108 y z) ∉
      (((Class.cv (nb060AlphaDummy098 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy098 y z))).fv) :=
  by
  simpa only [nb060AlphaDummy108] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy098 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy098 y z))).fv)
      0

theorem nb060_fresh_100 :
    (nb060AlphaDummy123) ∉ (((Class.cv (nb060AlphaDummy116))).fv) := by
  simpa only [nb060AlphaDummy123] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy116))).fv) 0

theorem nb060_fresh_101 :
    (nb060AlphaDummy124) ∉ (((Class.cv (nb060AlphaDummy116))).fv) := by
  simpa only [nb060AlphaDummy124] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy116))).fv) 1

theorem nb060_distinct_102 : (nb060AlphaDummy123) ≠ (nb060AlphaDummy124) := by
  simpa only [nb060AlphaDummy123, nb060AlphaDummy124] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy116))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_103 (x : Var) (z : Var) :
    (nb060AlphaDummy125 x z) ∉ (((Class.cv (nb060AlphaDummy118 x z))).fv) := by
  simpa only [nb060AlphaDummy125] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy118 x z))).fv) 0

theorem nb060_fresh_104 (x : Var) (z : Var) :
    (nb060AlphaDummy126 x z) ∉ (((Class.cv (nb060AlphaDummy118 x z))).fv) := by
  simpa only [nb060AlphaDummy126] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy118 x z))).fv) 1

theorem nb060_distinct_105 (x : Var) (z : Var) :
    (nb060AlphaDummy125 x z) ≠ (nb060AlphaDummy126 x z) := by
  simpa only [nb060AlphaDummy125, nb060AlphaDummy126] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy118 x z))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb060_fresh_106 :
    (nb060AlphaDummy129) ∉
      (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy129] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) 0

theorem nb060_fresh_107 :
    (nb060AlphaDummy130) ∉
      (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy130] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) 1

theorem nb060_fresh_108 :
    (nb060AlphaDummy131) ∉
      (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy131] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) 2

theorem nb060_distinct_109 : (nb060AlphaDummy129) ≠ (nb060AlphaDummy130) := by
  simpa only [nb060AlphaDummy129, nb060AlphaDummy130] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb060_distinct_110 : (nb060AlphaDummy129) ≠ (nb060AlphaDummy131) := by
  simpa only [nb060AlphaDummy129, nb060AlphaDummy131] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb060_distinct_111 : (nb060AlphaDummy130) ≠ (nb060AlphaDummy131) := by
  simpa only [nb060AlphaDummy130, nb060AlphaDummy131] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb060_fresh_112 (x : Var) (z : Var) :
    (nb060AlphaDummy132 x z) ∉
      (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy132] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) 0

theorem nb060_fresh_113 (x : Var) (z : Var) :
    (nb060AlphaDummy133 x z) ∉
      (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy133] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) 1

theorem nb060_fresh_114 (x : Var) (z : Var) :
    (nb060AlphaDummy134 x z) ∉
      (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb060AlphaDummy134] using
    freshVar_not_mem (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) 2

theorem nb060_distinct_115 (x : Var) (z : Var) :
    (nb060AlphaDummy132 x z) ≠ (nb060AlphaDummy133 x z) := by
  simpa only [nb060AlphaDummy132, nb060AlphaDummy133] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb060_distinct_116 (x : Var) (z : Var) :
    (nb060AlphaDummy132 x z) ≠ (nb060AlphaDummy134 x z) := by
  simpa only [nb060AlphaDummy132, nb060AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb060_distinct_117 (x : Var) (z : Var) :
    (nb060AlphaDummy133 x z) ≠ (nb060AlphaDummy134 x z) := by
  simpa only [nb060AlphaDummy133, nb060AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb060_fresh_118 :
    (nb060AlphaDummy141) ∉
      (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy130))).fv) :=
  by
  simpa only [nb060AlphaDummy141] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy130))).fv)
      0

theorem nb060_fresh_119 :
    (nb060AlphaDummy137) ∉
      (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv) :=
  by
  simpa only [nb060AlphaDummy137] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv)
      0

theorem nb060_fresh_120 :
    (nb060AlphaDummy143) ∉
      (((Class.cv (nb060AlphaDummy131))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv) :=
  by
  simpa only [nb060AlphaDummy143] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy131))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv)
      0

theorem nb060_fresh_121 (x : Var) (z : Var) :
    (nb060AlphaDummy142 x z) ∉
      (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy133 x z))).fv) :=
  by
  simpa only [nb060AlphaDummy142] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy133 x z))).fv)
      0

theorem nb060_fresh_122 (x : Var) (z : Var) :
    (nb060AlphaDummy138 x z) ∉
      (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy134 x z))).fv) :=
  by
  simpa only [nb060AlphaDummy138] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy134 x z))).fv)
      0

theorem nb060_fresh_123 (x : Var) (z : Var) :
    (nb060AlphaDummy144 x z) ∉
      (((Class.cv (nb060AlphaDummy134 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy134 x z))).fv) :=
  by
  simpa only [nb060AlphaDummy144] using
    freshVar_not_mem
      (((Class.cv (nb060AlphaDummy134 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy134 x z))).fv)
      0

theorem nb060_fresh_124 (r : Var) (a : Var) :
    (nb060AlphaDummy009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb060AlphaDummy009] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb060_fresh_125 (r : Var) (a : Var) :
    (nb060AlphaDummy010 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb060AlphaDummy010] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb060_distinct_126 (r : Var) (a : Var) :
    (nb060AlphaDummy009 r a) ≠ (nb060AlphaDummy010 r a) := by
  simpa only [nb060AlphaDummy009, nb060AlphaDummy010] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_127 (x : Var) (y : Var) :
    (nb060AlphaDummy045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb060AlphaDummy045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb060_fresh_128 (x : Var) (y : Var) :
    (nb060AlphaDummy046 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb060AlphaDummy046] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb060_distinct_129 (x : Var) (y : Var) :
    (nb060AlphaDummy045 x y) ≠ (nb060AlphaDummy046 x y) := by
  simpa only [nb060AlphaDummy045, nb060AlphaDummy046] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_130 (x : Var) (z : Var) :
    (nb060AlphaDummy117 x z) ∉ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060AlphaDummy117] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 0

theorem nb060_fresh_131 (x : Var) (z : Var) :
    (nb060AlphaDummy118 x z) ∉ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060AlphaDummy118] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 1

theorem nb060_distinct_132 (x : Var) (z : Var) :
    (nb060AlphaDummy117 x z) ≠ (nb060AlphaDummy118 x z) := by
  simpa only [nb060AlphaDummy117, nb060AlphaDummy118] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_133 (y : Var) (z : Var) :
    (nb060AlphaDummy081 y z) ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060AlphaDummy081] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0

theorem nb060_fresh_134 (y : Var) (z : Var) :
    (nb060AlphaDummy082 y z) ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060AlphaDummy082] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1

theorem nb060_distinct_135 (y : Var) (z : Var) :
    (nb060AlphaDummy081 y z) ≠ (nb060AlphaDummy082 y z) := by
  simpa only [nb060AlphaDummy081, nb060AlphaDummy082] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_136 :
    (nb060AlphaDummy019) ∉
      (((Wff.classMem (Class.cv (nb060AlphaDummy015)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy015)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy015))).fv) :=
  by
  simpa only [nb060AlphaDummy019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060AlphaDummy015)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy015)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy015))).fv)
      0

theorem nb060_fresh_137 (r : Var) (a : Var) :
    (nb060AlphaDummy020 r a) ∉
      (((Wff.classMem (Class.cv (nb060AlphaDummy017 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy017 r a)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy017 r a))).fv) :=
  by
  simpa only [nb060AlphaDummy020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060AlphaDummy017 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy017 r a)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy017 r a))).fv)
      0

theorem nb060_fresh_138 :
    (nb060AlphaDummy055) ∉
      (((Wff.classMem (Class.cv (nb060AlphaDummy051)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy051)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy051))).fv) :=
  by
  simpa only [nb060AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060AlphaDummy051)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy051)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy051))).fv)
      0

theorem nb060_fresh_139 (x : Var) (y : Var) :
    (nb060AlphaDummy056 x y) ∉
      (((Wff.classMem (Class.cv (nb060AlphaDummy053 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy053 x y)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy053 x y))).fv) :=
  by
  simpa only [nb060AlphaDummy056] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060AlphaDummy053 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy053 x y)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy053 x y))).fv)
      0

theorem nb060_fresh_140 :
    (nb060AlphaDummy091) ∉
      (((Wff.classMem (Class.cv (nb060AlphaDummy087)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy087)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy087))).fv) :=
  by
  simpa only [nb060AlphaDummy091] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060AlphaDummy087)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy087)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy087))).fv)
      0

theorem nb060_fresh_141 (y : Var) (z : Var) :
    (nb060AlphaDummy092 y z) ∉
      (((Wff.classMem (Class.cv (nb060AlphaDummy089 y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy089 y z)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy089 y z))).fv) :=
  by
  simpa only [nb060AlphaDummy092] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060AlphaDummy089 y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy089 y z)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy089 y z))).fv)
      0

theorem nb060_fresh_142 :
    (nb060AlphaDummy127) ∉
      (((Wff.classMem (Class.cv (nb060AlphaDummy123)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy123)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy123))).fv) :=
  by
  simpa only [nb060AlphaDummy127] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060AlphaDummy123)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy123)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy123))).fv)
      0

theorem nb060_fresh_143 (x : Var) (z : Var) :
    (nb060AlphaDummy128 x z) ∉
      (((Wff.classMem (Class.cv (nb060AlphaDummy125 x z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy125 x z)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy125 x z))).fv) :=
  by
  simpa only [nb060AlphaDummy128] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb060AlphaDummy125 x z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy125 x z)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy125 x z))).fv)
      0

theorem nb060_fresh_144 :
    (nb060AlphaDummy011) ∉
      (((synCcompl (Class.cab (nb060AlphaDummy007)
              (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
                (Wff.classEq (Class.cv (nb060AlphaDummy007))
                  (synCphi (Class.cv (nb060AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy007)
              (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
                (Wff.classEq (Class.cv (nb060AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb060AlphaDummy007)
              (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
                (Wff.classEq (Class.cv (nb060AlphaDummy007))
                  (synCphi (Class.cv (nb060AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy007)
              (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
                (Wff.classEq (Class.cv (nb060AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb060_fresh_145 (r : Var) (a : Var) :
    (nb060AlphaDummy012 r a) ∉
      (((synCcompl (Class.cab (nb060AlphaDummy009 r a)
              (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                  (synCphi (Class.cv (nb060AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy009 r a)
              (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy012] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb060AlphaDummy009 r a)
              (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                  (synCphi (Class.cv (nb060AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy009 r a)
              (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb060_fresh_146 :
    (nb060AlphaDummy047) ∉
      (((synCcompl (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCphi (Class.cv (nb060AlphaDummy044)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCphi (Class.cv (nb060AlphaDummy044)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb060_fresh_147 (x : Var) (y : Var) :
    (nb060AlphaDummy048 x y) ∉
      (((synCcompl (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCphi (Class.cv (nb060AlphaDummy046 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy048] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCphi (Class.cv (nb060AlphaDummy046 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb060_fresh_148 :
    (nb060AlphaDummy083) ∉
      (((synCcompl (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCphi (Class.cv (nb060AlphaDummy080)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy083] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCphi (Class.cv (nb060AlphaDummy080)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                    (synCsn (synC0c)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part003`. -/


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

theorem nb060_fresh_149 (y : Var) (z : Var) :
    (nb060AlphaDummy084 y z) ∉
      (((synCcompl (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCphi (Class.cv (nb060AlphaDummy082 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy084] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCphi (Class.cv (nb060AlphaDummy082 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb060_fresh_150 :
    (nb060AlphaDummy119) ∉
      (((synCcompl (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCphi (Class.cv (nb060AlphaDummy116)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy119] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCphi (Class.cv (nb060AlphaDummy116)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb060_fresh_151 (x : Var) (z : Var) :
    (nb060AlphaDummy120 x z) ∉
      (((synCcompl (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCphi (Class.cv (nb060AlphaDummy118 x z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy120] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCphi (Class.cv (nb060AlphaDummy118 x z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb060_fresh_152 :
    (nb060AlphaDummy031) ∉
      (((synCcompl (Class.cv (nb060AlphaDummy022)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy023)))).fv) :=
  by
  simpa only [nb060AlphaDummy031] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb060AlphaDummy022)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy023)))).fv)
      0

theorem nb060_fresh_153 (r : Var) (a : Var) :
    (nb060AlphaDummy032 r a) ∉
      (((synCcompl (Class.cv (nb060AlphaDummy025 r a)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy026 r a)))).fv) :=
  by
  simpa only [nb060AlphaDummy032] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb060AlphaDummy025 r a)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy026 r a)))).fv)
      0

theorem nb060_fresh_154 :
    (nb060AlphaDummy067) ∉
      (((synCcompl (Class.cv (nb060AlphaDummy058)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy059)))).fv) :=
  by
  simpa only [nb060AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb060AlphaDummy058)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy059)))).fv)
      0

theorem nb060_fresh_155 (x : Var) (y : Var) :
    (nb060AlphaDummy068 x y) ∉
      (((synCcompl (Class.cv (nb060AlphaDummy061 x y)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy062 x y)))).fv) :=
  by
  simpa only [nb060AlphaDummy068] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb060AlphaDummy061 x y)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy062 x y)))).fv)
      0

theorem nb060_fresh_156 :
    (nb060AlphaDummy103) ∉
      (((synCcompl (Class.cv (nb060AlphaDummy094)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy095)))).fv) :=
  by
  simpa only [nb060AlphaDummy103] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb060AlphaDummy094)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy095)))).fv)
      0

theorem nb060_fresh_157 (y : Var) (z : Var) :
    (nb060AlphaDummy104 y z) ∉
      (((synCcompl (Class.cv (nb060AlphaDummy097 y z)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy098 y z)))).fv) :=
  by
  simpa only [nb060AlphaDummy104] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb060AlphaDummy097 y z)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy098 y z)))).fv)
      0

theorem nb060_fresh_158 :
    (nb060AlphaDummy139) ∉
      (((synCcompl (Class.cv (nb060AlphaDummy130)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy131)))).fv) :=
  by
  simpa only [nb060AlphaDummy139] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb060AlphaDummy130)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy131)))).fv)
      0

theorem nb060_fresh_159 (x : Var) (z : Var) :
    (nb060AlphaDummy140 x z) ∉
      (((synCcompl (Class.cv (nb060AlphaDummy133 x z)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy134 x z)))).fv) :=
  by
  simpa only [nb060AlphaDummy140] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb060AlphaDummy133 x z)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy134 x z)))).fv)
      0

theorem nb060_fresh_160 :
    (nb060AlphaDummy039) ∉
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb060AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb060_fresh_161 (r : Var) (a : Var) :
    (nb060AlphaDummy040 r a) ∉
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy010 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb060AlphaDummy040] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy010 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb060_fresh_162 :
    (nb060AlphaDummy075) ∉
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy044))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb060AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy044))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb060_fresh_163 (x : Var) (y : Var) :
    (nb060AlphaDummy076 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy046 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb060AlphaDummy076] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy046 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb060_fresh_164 :
    (nb060AlphaDummy111) ∉
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy080))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb060AlphaDummy111] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy080))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb060_fresh_165 (y : Var) (z : Var) :
    (nb060AlphaDummy112 y z) ∉
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy082 y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb060AlphaDummy112] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy082 y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb060_fresh_166 :
    (nb060AlphaDummy147) ∉
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy116))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb060AlphaDummy147] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy116))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb060_fresh_167 (x : Var) (z : Var) :
    (nb060AlphaDummy148 x z) ∉
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy118 x z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb060AlphaDummy148] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy118 x z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb060_fresh_168 :
    (nb060AlphaDummy027) ∉
      (((synCnin (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy022))
            (Class.cv (nb060AlphaDummy023)))).fv) :=
  by
  simpa only [nb060AlphaDummy027] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023)))).fv)
      0

theorem nb060_fresh_169 (r : Var) (a : Var) :
    (nb060AlphaDummy028 r a) ∉
      (((synCnin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a)))).fv) :=
  by
  simpa only [nb060AlphaDummy028] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a)))).fv)
      0

theorem nb060_fresh_170 :
    (nb060AlphaDummy063) ∉
      (((synCnin (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy058))
            (Class.cv (nb060AlphaDummy059)))).fv) :=
  by
  simpa only [nb060AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059)))).fv)
      0

theorem nb060_fresh_171 (x : Var) (y : Var) :
    (nb060AlphaDummy064 x y) ∉
      (((synCnin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y)))).fv) :=
  by
  simpa only [nb060AlphaDummy064] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y)))).fv)
      0

theorem nb060_fresh_172 :
    (nb060AlphaDummy099) ∉
      (((synCnin (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy094))
            (Class.cv (nb060AlphaDummy095)))).fv) :=
  by
  simpa only [nb060AlphaDummy099] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095)))).fv)
      0

theorem nb060_fresh_173 (y : Var) (z : Var) :
    (nb060AlphaDummy100 y z) ∉
      (((synCnin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z)))).fv) :=
  by
  simpa only [nb060AlphaDummy100] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z)))).fv)
      0

theorem nb060_fresh_174 :
    (nb060AlphaDummy135) ∉
      (((synCnin (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy130))
            (Class.cv (nb060AlphaDummy131)))).fv) :=
  by
  simpa only [nb060AlphaDummy135] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131)))).fv)
      0

theorem nb060_fresh_175 (x : Var) (z : Var) :
    (nb060AlphaDummy136 x z) ∉
      (((synCnin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z)))).fv) :=
  by
  simpa only [nb060AlphaDummy136] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z)))).fv)
      0

theorem nb060_fresh_176 :
    (nb060AlphaDummy041) ∉
      (((synCphi (Class.cv (nb060AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy008)))).fv) :=
  by
  simpa only [nb060AlphaDummy041] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb060AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy008)))).fv)
      0

theorem nb060_fresh_177 (r : Var) (a : Var) :
    (nb060AlphaDummy042 r a) ∉
      (((synCphi (Class.cv (nb060AlphaDummy010 r a)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy010 r a)))).fv) :=
  by
  simpa only [nb060AlphaDummy042] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb060AlphaDummy010 r a)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy010 r a)))).fv)
      0

theorem nb060_fresh_178 :
    (nb060AlphaDummy077) ∉
      (((synCphi (Class.cv (nb060AlphaDummy044)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy044)))).fv) :=
  by
  simpa only [nb060AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb060AlphaDummy044)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy044)))).fv)
      0

theorem nb060_fresh_179 (x : Var) (y : Var) :
    (nb060AlphaDummy078 x y) ∉
      (((synCphi (Class.cv (nb060AlphaDummy046 x y)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy046 x y)))).fv) :=
  by
  simpa only [nb060AlphaDummy078] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb060AlphaDummy046 x y)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy046 x y)))).fv)
      0

theorem nb060_fresh_180 :
    (nb060AlphaDummy113) ∉
      (((synCphi (Class.cv (nb060AlphaDummy080)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy080)))).fv) :=
  by
  simpa only [nb060AlphaDummy113] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb060AlphaDummy080)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy080)))).fv)
      0

theorem nb060_fresh_181 (y : Var) (z : Var) :
    (nb060AlphaDummy114 y z) ∉
      (((synCphi (Class.cv (nb060AlphaDummy082 y z)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy082 y z)))).fv) :=
  by
  simpa only [nb060AlphaDummy114] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb060AlphaDummy082 y z)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy082 y z)))).fv)
      0

theorem nb060_fresh_182 :
    (nb060AlphaDummy149) ∉
      (((synCphi (Class.cv (nb060AlphaDummy116)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy116)))).fv) :=
  by
  simpa only [nb060AlphaDummy149] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb060AlphaDummy116)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy116)))).fv)
      0

theorem nb060_fresh_183 (x : Var) (z : Var) :
    (nb060AlphaDummy150 x z) ∉
      (((synCphi (Class.cv (nb060AlphaDummy118 x z)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy118 x z)))).fv) :=
  by
  simpa only [nb060AlphaDummy150] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb060AlphaDummy118 x z)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy118 x z)))).fv)
      0

theorem nb060_fresh_184 :
    (nb060AlphaDummy005) ∉
      (({(nb060AlphaDummy001)} : Finset Var) ∪ ({(nb060AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb060AlphaDummy002) (Class.cv (nb060AlphaDummy000))
            (synWral (nb060AlphaDummy003) (Class.cv (nb060AlphaDummy000))
              (synWral (nb060AlphaDummy004) (Class.cv (nb060AlphaDummy000)) (Wff.imp
                  (synWa (synWbr (Class.cv (nb060AlphaDummy002))
                      (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy003)))
                    (synWbr (Class.cv (nb060AlphaDummy003))
                      (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy004))))
                  (synWbr (Class.cv (nb060AlphaDummy002)) (Class.cv (nb060AlphaDummy001))
                    (Class.cv (nb060AlphaDummy004)))))))).fv) :=
  by
  simpa only [nb060AlphaDummy005] using
    freshVar_not_mem
      (({(nb060AlphaDummy001)} : Finset Var) ∪ ({(nb060AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb060AlphaDummy002) (Class.cv (nb060AlphaDummy000))
            (synWral (nb060AlphaDummy003) (Class.cv (nb060AlphaDummy000))
              (synWral (nb060AlphaDummy004) (Class.cv (nb060AlphaDummy000)) (Wff.imp
                  (synWa (synWbr (Class.cv (nb060AlphaDummy002))
                      (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy003)))
                    (synWbr (Class.cv (nb060AlphaDummy003))
                      (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy004))))
                  (synWbr (Class.cv (nb060AlphaDummy002)) (Class.cv (nb060AlphaDummy001))
                    (Class.cv (nb060AlphaDummy004)))))))).fv)
      0

theorem nb060_fresh_185 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    (nb060AlphaDummy006 x y z r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (synWral z (Class.cv a) (Wff.imp
                  (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                    (synWbr (Class.cv y) (Class.cv r) (Class.cv z)))
                  (synWbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) :=
  by
  simpa only [nb060AlphaDummy006] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (synWral z (Class.cv a) (Wff.imp
                  (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                    (synWbr (Class.cv y) (Class.cv r) (Class.cv z)))
                  (synWbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv)
      0

theorem nb060_fresh_186 : (nb060AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb060_fresh_187 : (nb060AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb060_fresh_188 : (nb060AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb060_fresh_189 : (nb060AlphaDummy003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060AlphaDummy003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb060_fresh_190 : (nb060AlphaDummy004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060AlphaDummy004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb060_distinct_191 : (nb060AlphaDummy000) ≠ (nb060AlphaDummy001) := by
  simpa only [nb060AlphaDummy000, nb060AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_192 : (nb060AlphaDummy000) ≠ (nb060AlphaDummy002) := by
  simpa only [nb060AlphaDummy000, nb060AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_193 : (nb060AlphaDummy000) ≠ (nb060AlphaDummy003) := by
  simpa only [nb060AlphaDummy000, nb060AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb060_distinct_194 : (nb060AlphaDummy000) ≠ (nb060AlphaDummy004) := by
  simpa only [nb060AlphaDummy000, nb060AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb060_distinct_195 : (nb060AlphaDummy001) ≠ (nb060AlphaDummy002) := by
  simpa only [nb060AlphaDummy001, nb060AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb060_distinct_196 : (nb060AlphaDummy001) ≠ (nb060AlphaDummy003) := by
  simpa only [nb060AlphaDummy001, nb060AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb060_distinct_197 : (nb060AlphaDummy001) ≠ (nb060AlphaDummy004) := by
  simpa only [nb060AlphaDummy001, nb060AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb060_distinct_198 : (nb060AlphaDummy002) ≠ (nb060AlphaDummy003) := by
  simpa only [nb060AlphaDummy002, nb060AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb060_distinct_199 : (nb060AlphaDummy002) ≠ (nb060AlphaDummy004) := by
  simpa only [nb060AlphaDummy002, nb060AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb060_distinct_200 : (nb060AlphaDummy003) ≠ (nb060AlphaDummy004) := by
  simpa only [nb060AlphaDummy003, nb060AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb060_support_mem_0000 :
    (nb060AlphaDummy001) ∈
      (({(nb060AlphaDummy001)} : Finset Var) ∪ ({(nb060AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb060AlphaDummy002) (Class.cv (nb060AlphaDummy000))
            (synWral (nb060AlphaDummy003) (Class.cv (nb060AlphaDummy000))
              (synWral (nb060AlphaDummy004) (Class.cv (nb060AlphaDummy000)) (Wff.imp
                  (synWa (synWbr (Class.cv (nb060AlphaDummy002))
                      (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy003)))
                    (synWbr (Class.cv (nb060AlphaDummy003))
                      (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy004))))
                  (synWbr (Class.cv (nb060AlphaDummy002)) (Class.cv (nb060AlphaDummy001))
                    (Class.cv (nb060AlphaDummy004)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (synWral z (Class.cv a) (Wff.imp
                  (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                    (synWbr (Class.cv y) (Class.cv r) (Class.cv z)))
                  (synWbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0002 :
    (nb060AlphaDummy000) ∈
      (({(nb060AlphaDummy001)} : Finset Var) ∪ ({(nb060AlphaDummy000)} : Finset Var) ∪
        ((synWral (nb060AlphaDummy002) (Class.cv (nb060AlphaDummy000))
            (synWral (nb060AlphaDummy003) (Class.cv (nb060AlphaDummy000))
              (synWral (nb060AlphaDummy004) (Class.cv (nb060AlphaDummy000)) (Wff.imp
                  (synWa (synWbr (Class.cv (nb060AlphaDummy002))
                      (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy003)))
                    (synWbr (Class.cv (nb060AlphaDummy003))
                      (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy004))))
                  (synWbr (Class.cv (nb060AlphaDummy002)) (Class.cv (nb060AlphaDummy001))
                    (Class.cv (nb060AlphaDummy004)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0003 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWral x (Class.cv a)
            (synWral y (Class.cv a) (synWral z (Class.cv a) (Wff.imp
                  (synWa (synWbr (Class.cv x) (Class.cv r) (Class.cv y))
                    (synWbr (Class.cv y) (Class.cv r) (Class.cv z)))
                  (synWbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0004 :
    (nb060AlphaDummy001) ∈
      (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0005 :
    (nb060AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb060AlphaDummy007)
              (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
                (Wff.classEq (Class.cv (nb060AlphaDummy007))
                  (synCphi (Class.cv (nb060AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy007)
              (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
                (Wff.classEq (Class.cv (nb060AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((synCcompl (Class.cab (nb060AlphaDummy009 r a)
              (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                  (synCphi (Class.cv (nb060AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy009 r a)
              (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0008 :
    (nb060AlphaDummy001) ∈
      (((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCphi (Class.cv (nb060AlphaDummy008))))))).fv ∪
        ((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCphi (Class.cv (nb060AlphaDummy008))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCphi (Class.cv (nb060AlphaDummy010 r a))))))).fv ∪
        ((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCphi (Class.cv (nb060AlphaDummy010 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0010 :
    (nb060AlphaDummy008) ∈ (((Class.cv (nb060AlphaDummy008))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0011 (r : Var) (a : Var) :
    (nb060AlphaDummy010 r a) ∈ (((Class.cv (nb060AlphaDummy010 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0012 :
    (nb060AlphaDummy015) ∈
      (((Wff.classMem (Class.cv (nb060AlphaDummy015)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy015)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy015))).fv) :=
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

theorem nb060_support_mem_0013 (r : Var) (a : Var) :
    (nb060AlphaDummy017 r a) ∈
      (((Wff.classMem (Class.cv (nb060AlphaDummy017 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy017 r a)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy017 r a))).fv) :=
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

theorem nb060_support_mem_0014 :
    (nb060AlphaDummy015) ∈
      (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0015 (r : Var) (a : Var) :
    (nb060AlphaDummy017 r a) ∈
      (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0016 :
    (nb060AlphaDummy022) ∈
      (((synCnin (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy022))
            (Class.cv (nb060AlphaDummy023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0017 (r : Var) (a : Var) :
    (nb060AlphaDummy025 r a) ∈
      (((synCnin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0018 :
    (nb060AlphaDummy022) ∈
      (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0019 (r : Var) (a : Var) :
    (nb060AlphaDummy025 r a) ∈
      (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0020 :
    (nb060AlphaDummy023) ∈
      (((synCnin (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy022))
            (Class.cv (nb060AlphaDummy023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0021 (r : Var) (a : Var) :
    (nb060AlphaDummy026 r a) ∈
      (((synCnin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0022 :
    (nb060AlphaDummy023) ∈
      (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0023 (r : Var) (a : Var) :
    (nb060AlphaDummy026 r a) ∈
      (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0024 :
    (nb060AlphaDummy022) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy022)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0025 (r : Var) (a : Var) :
    (nb060AlphaDummy025 r a) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy025 r a)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0026 :
    (nb060AlphaDummy022) ∈
      (((Class.cv (nb060AlphaDummy022))).fv ∪ ((Class.cv (nb060AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0027 (r : Var) (a : Var) :
    (nb060AlphaDummy025 r a) ∈
      (((Class.cv (nb060AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0028 :
    (nb060AlphaDummy023) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy022)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0029 (r : Var) (a : Var) :
    (nb060AlphaDummy026 r a) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy025 r a)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0030 :
    (nb060AlphaDummy023) ∈
      (((Class.cv (nb060AlphaDummy023))).fv ∪ ((Class.cv (nb060AlphaDummy023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0031 (r : Var) (a : Var) :
    (nb060AlphaDummy026 r a) ∈
      (((Class.cv (nb060AlphaDummy026 r a))).fv ∪
        ((Class.cv (nb060AlphaDummy026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0032 :
    (nb060AlphaDummy000) ∈
      (((Class.cv (nb060AlphaDummy001))).fv ∪ ((Class.cv (nb060AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0033 :
    (nb060AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb060AlphaDummy007)
              (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy001))
                (Wff.classEq (Class.cv (nb060AlphaDummy007))
                  (synCphi (Class.cv (nb060AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy007)
              (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
                (Wff.classEq (Class.cv (nb060AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((synCcompl (Class.cab (nb060AlphaDummy009 r a)
              (synWrex (nb060AlphaDummy010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                  (synCphi (Class.cv (nb060AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy009 r a)
              (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0036 :
    (nb060AlphaDummy000) ∈
      (((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy007)
            (synWrex (nb060AlphaDummy008) (Class.cv (nb060AlphaDummy000))
              (Wff.classEq (Class.cv (nb060AlphaDummy007))
                (synCun (synCphi (Class.cv (nb060AlphaDummy008)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy009 r a)
            (synWrex (nb060AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb060AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0038 :
    (nb060AlphaDummy008) ∈
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0039 (r : Var) (a : Var) :
    (nb060AlphaDummy010 r a) ∈
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy010 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0040 :
    (nb060AlphaDummy008) ∈
      (((synCphi (Class.cv (nb060AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy008)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0041 (r : Var) (a : Var) :
    (nb060AlphaDummy010 r a) ∈
      (((synCphi (Class.cv (nb060AlphaDummy010 r a)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy010 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0042 :
    (nb060AlphaDummy002) ∈
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0043 :
    (nb060AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCphi (Class.cv (nb060AlphaDummy044)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0044 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0045 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCphi (Class.cv (nb060AlphaDummy046 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0046 :
    (nb060AlphaDummy002) ∈
      (((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCphi (Class.cv (nb060AlphaDummy044))))))).fv ∪
        ((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCphi (Class.cv (nb060AlphaDummy044))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0047 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCphi (Class.cv (nb060AlphaDummy046 x y))))))).fv ∪
        ((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCphi (Class.cv (nb060AlphaDummy046 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0048 :
    (nb060AlphaDummy044) ∈ (((Class.cv (nb060AlphaDummy044))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0049 (x : Var) (y : Var) :
    (nb060AlphaDummy046 x y) ∈ (((Class.cv (nb060AlphaDummy046 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0050 :
    (nb060AlphaDummy051) ∈
      (((Wff.classMem (Class.cv (nb060AlphaDummy051)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy051)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy051))).fv) :=
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

theorem nb060_support_mem_0051 (x : Var) (y : Var) :
    (nb060AlphaDummy053 x y) ∈
      (((Wff.classMem (Class.cv (nb060AlphaDummy053 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy053 x y)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy053 x y))).fv) :=
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

theorem nb060_support_mem_0052 :
    (nb060AlphaDummy051) ∈
      (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0053 (x : Var) (y : Var) :
    (nb060AlphaDummy053 x y) ∈
      (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0054 :
    (nb060AlphaDummy058) ∈
      (((synCnin (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy058))
            (Class.cv (nb060AlphaDummy059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0055 (x : Var) (y : Var) :
    (nb060AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0056 :
    (nb060AlphaDummy058) ∈
      (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0057 (x : Var) (y : Var) :
    (nb060AlphaDummy061 x y) ∈
      (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy062 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0058 :
    (nb060AlphaDummy059) ∈
      (((synCnin (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy058))
            (Class.cv (nb060AlphaDummy059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0059 (x : Var) (y : Var) :
    (nb060AlphaDummy062 x y) ∈
      (((synCnin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0060 :
    (nb060AlphaDummy059) ∈
      (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0061 (x : Var) (y : Var) :
    (nb060AlphaDummy062 x y) ∈
      (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy062 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0062 :
    (nb060AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy058)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0063 (x : Var) (y : Var) :
    (nb060AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy061 x y)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy062 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0064 :
    (nb060AlphaDummy058) ∈
      (((Class.cv (nb060AlphaDummy058))).fv ∪ ((Class.cv (nb060AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0065 (x : Var) (y : Var) :
    (nb060AlphaDummy061 x y) ∈
      (((Class.cv (nb060AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0066 :
    (nb060AlphaDummy059) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy058)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0067 (x : Var) (y : Var) :
    (nb060AlphaDummy062 x y) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy061 x y)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy062 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0068 :
    (nb060AlphaDummy059) ∈
      (((Class.cv (nb060AlphaDummy059))).fv ∪ ((Class.cv (nb060AlphaDummy059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0069 (x : Var) (y : Var) :
    (nb060AlphaDummy062 x y) ∈
      (((Class.cv (nb060AlphaDummy062 x y))).fv ∪
        ((Class.cv (nb060AlphaDummy062 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0070 :
    (nb060AlphaDummy003) ∈
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0071 :
    (nb060AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy002))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCphi (Class.cv (nb060AlphaDummy044)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0072 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0073 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCphi (Class.cv (nb060AlphaDummy046 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0074 :
    (nb060AlphaDummy003) ∈
      (((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0075 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0076 :
    (nb060AlphaDummy044) ∈
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy044))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0077 (x : Var) (y : Var) :
    (nb060AlphaDummy046 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy046 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0078 :
    (nb060AlphaDummy044) ∈
      (((synCphi (Class.cv (nb060AlphaDummy044)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy044)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0079 (x : Var) (y : Var) :
    (nb060AlphaDummy046 x y) ∈
      (((synCphi (Class.cv (nb060AlphaDummy046 x y)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy046 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0080 :
    (nb060AlphaDummy003) ∈
      (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0081 :
    (nb060AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCphi (Class.cv (nb060AlphaDummy080)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0082 (y : Var) (z : Var) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0083 (y : Var) (z : Var) :
    y ∈
      (((synCcompl (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCphi (Class.cv (nb060AlphaDummy082 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0084 :
    (nb060AlphaDummy003) ∈
      (((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCphi (Class.cv (nb060AlphaDummy080))))))).fv ∪
        ((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCphi (Class.cv (nb060AlphaDummy080))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part004`. -/


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

theorem nb060_support_mem_0085 (y : Var) (z : Var) :
    y ∈
      (((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCphi (Class.cv (nb060AlphaDummy082 y z))))))).fv ∪
        ((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCphi (Class.cv (nb060AlphaDummy082 y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0086 :
    (nb060AlphaDummy080) ∈ (((Class.cv (nb060AlphaDummy080))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0087 (y : Var) (z : Var) :
    (nb060AlphaDummy082 y z) ∈ (((Class.cv (nb060AlphaDummy082 y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0088 :
    (nb060AlphaDummy087) ∈
      (((Wff.classMem (Class.cv (nb060AlphaDummy087)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy087)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy087))).fv) :=
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

theorem nb060_support_mem_0089 (y : Var) (z : Var) :
    (nb060AlphaDummy089 y z) ∈
      (((Wff.classMem (Class.cv (nb060AlphaDummy089 y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy089 y z)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy089 y z))).fv) :=
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

theorem nb060_support_mem_0090 :
    (nb060AlphaDummy087) ∈
      (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0091 (y : Var) (z : Var) :
    (nb060AlphaDummy089 y z) ∈
      (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0092 :
    (nb060AlphaDummy094) ∈
      (((synCnin (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy094))
            (Class.cv (nb060AlphaDummy095)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0093 (y : Var) (z : Var) :
    (nb060AlphaDummy097 y z) ∈
      (((synCnin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0094 :
    (nb060AlphaDummy094) ∈
      (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0095 (y : Var) (z : Var) :
    (nb060AlphaDummy097 y z) ∈
      (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy098 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0096 :
    (nb060AlphaDummy095) ∈
      (((synCnin (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy094))
            (Class.cv (nb060AlphaDummy095)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0097 (y : Var) (z : Var) :
    (nb060AlphaDummy098 y z) ∈
      (((synCnin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0098 :
    (nb060AlphaDummy095) ∈
      (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0099 (y : Var) (z : Var) :
    (nb060AlphaDummy098 y z) ∈
      (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy098 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0100 :
    (nb060AlphaDummy094) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy094)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy095)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0101 (y : Var) (z : Var) :
    (nb060AlphaDummy097 y z) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy097 y z)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy098 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0102 :
    (nb060AlphaDummy094) ∈
      (((Class.cv (nb060AlphaDummy094))).fv ∪ ((Class.cv (nb060AlphaDummy094))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0103 (y : Var) (z : Var) :
    (nb060AlphaDummy097 y z) ∈
      (((Class.cv (nb060AlphaDummy097 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy097 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0104 :
    (nb060AlphaDummy095) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy094)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy095)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0105 (y : Var) (z : Var) :
    (nb060AlphaDummy098 y z) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy097 y z)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy098 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0106 :
    (nb060AlphaDummy095) ∈
      (((Class.cv (nb060AlphaDummy095))).fv ∪ ((Class.cv (nb060AlphaDummy095))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0107 (y : Var) (z : Var) :
    (nb060AlphaDummy098 y z) ∈
      (((Class.cv (nb060AlphaDummy098 y z))).fv ∪
        ((Class.cv (nb060AlphaDummy098 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0108 :
    (nb060AlphaDummy004) ∈
      (((Class.cv (nb060AlphaDummy003))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0109 :
    (nb060AlphaDummy004) ∈
      (((synCcompl (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCphi (Class.cv (nb060AlphaDummy080)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0110 (y : Var) (z : Var) :
    z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0111 (y : Var) (z : Var) :
    z ∈
      (((synCcompl (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCphi (Class.cv (nb060AlphaDummy082 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0112 :
    (nb060AlphaDummy004) ∈
      (((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy079)
            (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy079))
                (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0113 (y : Var) (z : Var) :
    z ∈
      (((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy081 y z)
            (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0114 :
    (nb060AlphaDummy080) ∈
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy080))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0115 (y : Var) (z : Var) :
    (nb060AlphaDummy082 y z) ∈
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy082 y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0116 :
    (nb060AlphaDummy080) ∈
      (((synCphi (Class.cv (nb060AlphaDummy080)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy080)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0117 (y : Var) (z : Var) :
    (nb060AlphaDummy082 y z) ∈
      (((synCphi (Class.cv (nb060AlphaDummy082 y z)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy082 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0118 :
    (nb060AlphaDummy002) ∈
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0119 :
    (nb060AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCphi (Class.cv (nb060AlphaDummy116)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0120 (x : Var) (z : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0121 (x : Var) (z : Var) :
    x ∈
      (((synCcompl (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCphi (Class.cv (nb060AlphaDummy118 x z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0122 :
    (nb060AlphaDummy002) ∈
      (((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCphi (Class.cv (nb060AlphaDummy116))))))).fv ∪
        ((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCphi (Class.cv (nb060AlphaDummy116))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0123 (x : Var) (z : Var) :
    x ∈
      (((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCphi (Class.cv (nb060AlphaDummy118 x z))))))).fv ∪
        ((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCphi (Class.cv (nb060AlphaDummy118 x z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0124 :
    (nb060AlphaDummy116) ∈ (((Class.cv (nb060AlphaDummy116))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0125 (x : Var) (z : Var) :
    (nb060AlphaDummy118 x z) ∈ (((Class.cv (nb060AlphaDummy118 x z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0126 :
    (nb060AlphaDummy123) ∈
      (((Wff.classMem (Class.cv (nb060AlphaDummy123)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy123)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy123))).fv) :=
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

theorem nb060_support_mem_0127 (x : Var) (z : Var) :
    (nb060AlphaDummy125 x z) ∈
      (((Wff.classMem (Class.cv (nb060AlphaDummy125 x z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb060AlphaDummy125 x z)) (synC1c))).fv ∪
        ((Class.cv (nb060AlphaDummy125 x z))).fv) :=
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

theorem nb060_support_mem_0128 :
    (nb060AlphaDummy123) ∈
      (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0129 (x : Var) (z : Var) :
    (nb060AlphaDummy125 x z) ∈
      (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0130 :
    (nb060AlphaDummy130) ∈
      (((synCnin (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy130))
            (Class.cv (nb060AlphaDummy131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0131 (x : Var) (z : Var) :
    (nb060AlphaDummy133 x z) ∈
      (((synCnin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0132 :
    (nb060AlphaDummy130) ∈
      (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0133 (x : Var) (z : Var) :
    (nb060AlphaDummy133 x z) ∈
      (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy134 x z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0134 :
    (nb060AlphaDummy131) ∈
      (((synCnin (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy130))
            (Class.cv (nb060AlphaDummy131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0135 (x : Var) (z : Var) :
    (nb060AlphaDummy134 x z) ∈
      (((synCnin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z)))).fv ∪
        ((synCnin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0136 :
    (nb060AlphaDummy131) ∈
      (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0137 (x : Var) (z : Var) :
    (nb060AlphaDummy134 x z) ∈
      (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy134 x z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0138 :
    (nb060AlphaDummy130) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy130)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0139 (x : Var) (z : Var) :
    (nb060AlphaDummy133 x z) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy133 x z)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy134 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0140 :
    (nb060AlphaDummy130) ∈
      (((Class.cv (nb060AlphaDummy130))).fv ∪ ((Class.cv (nb060AlphaDummy130))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0141 (x : Var) (z : Var) :
    (nb060AlphaDummy133 x z) ∈
      (((Class.cv (nb060AlphaDummy133 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy133 x z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0142 :
    (nb060AlphaDummy131) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy130)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0143 (x : Var) (z : Var) :
    (nb060AlphaDummy134 x z) ∈
      (((synCcompl (Class.cv (nb060AlphaDummy133 x z)))).fv ∪
        ((synCcompl (Class.cv (nb060AlphaDummy134 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0144 :
    (nb060AlphaDummy131) ∈
      (((Class.cv (nb060AlphaDummy131))).fv ∪ ((Class.cv (nb060AlphaDummy131))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0145 (x : Var) (z : Var) :
    (nb060AlphaDummy134 x z) ∈
      (((Class.cv (nb060AlphaDummy134 x z))).fv ∪
        ((Class.cv (nb060AlphaDummy134 x z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0146 :
    (nb060AlphaDummy004) ∈
      (((Class.cv (nb060AlphaDummy002))).fv ∪ ((Class.cv (nb060AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0147 :
    (nb060AlphaDummy004) ∈
      (((synCcompl (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy002))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCphi (Class.cv (nb060AlphaDummy116)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0148 (x : Var) (z : Var) :
    z ∈ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0149 (x : Var) (z : Var) :
    z ∈
      (((synCcompl (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv x)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCphi (Class.cv (nb060AlphaDummy118 x z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0150 :
    (nb060AlphaDummy004) ∈
      (((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy115)
            (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
              (Wff.classEq (Class.cv (nb060AlphaDummy115))
                (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0151 (x : Var) (z : Var) :
    z ∈
      (((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb060AlphaDummy117 x z)
            (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
              (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0152 :
    (nb060AlphaDummy116) ∈
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy116))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0153 (x : Var) (z : Var) :
    (nb060AlphaDummy118 x z) ∈
      (((synCcompl (synCphi (Class.cv (nb060AlphaDummy118 x z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0154 :
    (nb060AlphaDummy116) ∈
      (((synCphi (Class.cv (nb060AlphaDummy116)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy116)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0155 (x : Var) (z : Var) :
    (nb060AlphaDummy118 x z) ∈
      (((synCphi (Class.cv (nb060AlphaDummy118 x z)))).fv ∪
        ((synCphi (Class.cv (nb060AlphaDummy118 x z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
