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

/-! Certificates from `NAR4C064C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_000`. -/
@[expose]
noncomputable def nb064AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_001`. -/
@[expose]
noncomputable def nb064AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_002`. -/
@[expose]
noncomputable def nb064AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_003`. -/
@[expose]
noncomputable def nb064AlphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_004`. -/
@[expose]
noncomputable def nb064AlphaDummy004 : Var :=
  (freshVar ((∅ : Finset Var)) 4)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_005`. -/
@[expose]
noncomputable def nb064AlphaDummy005 : Var :=
  (freshVar
    (({(nb064AlphaDummy001)} : Finset Var) ∪ ({(nb064AlphaDummy000)} : Finset Var) ∪
      ((Wff.all (nb064AlphaDummy002) (Wff.imp (synWa
              (synWss (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))
              (synWne (Class.cv (nb064AlphaDummy002)) (synC0)))
            (synWrex (nb064AlphaDummy004) (Class.cv (nb064AlphaDummy002))
              (synWral (nb064AlphaDummy003) (Class.cv (nb064AlphaDummy002)) (Wff.imp
                  (synWbr (Class.cv (nb064AlphaDummy003))
                    (Class.cv (nb064AlphaDummy001)) (Class.cv (nb064AlphaDummy004)))
                  (Wff.objEq (nb064AlphaDummy003) (nb064AlphaDummy004)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_006`. -/
@[expose]
noncomputable def nb064AlphaDummy006 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((Wff.all x (Wff.imp
            (synWa (synWss (Class.cv x) (Class.cv a)) (synWne (Class.cv x) (synC0)))
            (synWrex z (Class.cv x) (synWral y (Class.cv x)
                (Wff.imp (synWbr (Class.cv y) (Class.cv r) (Class.cv z))
                  (Wff.objEq y z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_007`. -/
@[expose]
noncomputable def nb064AlphaDummy007 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_008`. -/
@[expose]
noncomputable def nb064AlphaDummy008 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_009`. -/
@[expose]
noncomputable def nb064AlphaDummy009 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_010`. -/
@[expose]
noncomputable def nb064AlphaDummy010 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_011`. -/
@[expose]
noncomputable def nb064AlphaDummy011 : Var :=
  (freshVar (((synCcompl (Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCphi (Class.cv (nb064AlphaDummy008)))))))).fv ∪ ((synCcompl
          (Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_012`. -/
@[expose]
noncomputable def nb064AlphaDummy012 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCphi (Class.cv (nb064AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
          (Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_013`. -/
@[expose]
noncomputable def nb064AlphaDummy013 : Var :=
  (freshVar (((Class.cab (nb064AlphaDummy007)
          (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
            (Wff.classEq (Class.cv (nb064AlphaDummy007))
              (synCphi (Class.cv (nb064AlphaDummy008))))))).fv ∪
      ((Class.cab (nb064AlphaDummy007)
          (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
            (Wff.classEq (Class.cv (nb064AlphaDummy007))
              (synCphi (Class.cv (nb064AlphaDummy008))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_014`. -/
@[expose]
noncomputable def nb064AlphaDummy014 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb064AlphaDummy009 r a)
          (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
              (synCphi (Class.cv (nb064AlphaDummy010 r a))))))).fv ∪
      ((Class.cab (nb064AlphaDummy009 r a) (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
            (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
              (synCphi (Class.cv (nb064AlphaDummy010 r a))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_015`. -/
@[expose]
noncomputable def nb064AlphaDummy015 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy008))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_016`. -/
@[expose]
noncomputable def nb064AlphaDummy016 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy008))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_017`. -/
@[expose]
noncomputable def nb064AlphaDummy017 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy010 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_018`. -/
@[expose]
noncomputable def nb064AlphaDummy018 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy010 r a))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_019`. -/
@[expose]
noncomputable def nb064AlphaDummy019 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb064AlphaDummy015)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb064AlphaDummy015)) (synC1c))).fv ∪
      ((Class.cv (nb064AlphaDummy015))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_020`. -/
@[expose]
noncomputable def nb064AlphaDummy020 (r : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb064AlphaDummy017 r a)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb064AlphaDummy017 r a)) (synC1c))).fv ∪
      ((Class.cv (nb064AlphaDummy017 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_021`. -/
@[expose]
noncomputable def nb064AlphaDummy021 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_022`. -/
@[expose]
noncomputable def nb064AlphaDummy022 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_023`. -/
@[expose]
noncomputable def nb064AlphaDummy023 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_024`. -/
@[expose]
noncomputable def nb064AlphaDummy024 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_025`. -/
@[expose]
noncomputable def nb064AlphaDummy025 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_026`. -/
@[expose]
noncomputable def nb064AlphaDummy026 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_027`. -/
@[expose]
noncomputable def nb064AlphaDummy027 : Var :=
  (freshVar (((synCnin (Class.cv (nb064AlphaDummy022))
          (Class.cv (nb064AlphaDummy023)))).fv ∪
      ((synCnin (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_028`. -/
@[expose]
noncomputable def nb064AlphaDummy028 (r : Var) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb064AlphaDummy025 r a))
          (Class.cv (nb064AlphaDummy026 r a)))).fv ∪
      ((synCnin (Class.cv (nb064AlphaDummy025 r a))
          (Class.cv (nb064AlphaDummy026 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_029`. -/
@[expose]
noncomputable def nb064AlphaDummy029 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_030`. -/
@[expose]
noncomputable def nb064AlphaDummy030 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
      ((Class.cv (nb064AlphaDummy026 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_031`. -/
@[expose]
noncomputable def nb064AlphaDummy031 : Var :=
  (freshVar (((synCcompl (Class.cv (nb064AlphaDummy022)))).fv ∪
      ((synCcompl (Class.cv (nb064AlphaDummy023)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_032`. -/
@[expose]
noncomputable def nb064AlphaDummy032 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb064AlphaDummy025 r a)))).fv ∪
      ((synCcompl (Class.cv (nb064AlphaDummy026 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_033`. -/
@[expose]
noncomputable def nb064AlphaDummy033 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy022))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_034`. -/
@[expose]
noncomputable def nb064AlphaDummy034 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
      ((Class.cv (nb064AlphaDummy025 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_035`. -/
@[expose]
noncomputable def nb064AlphaDummy035 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy023))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_036`. -/
@[expose]
noncomputable def nb064AlphaDummy036 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy026 r a))).fv ∪
      ((Class.cv (nb064AlphaDummy026 r a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_037`. -/
@[expose]
noncomputable def nb064AlphaDummy037 : Var :=
  (freshVar (((Class.cab (nb064AlphaDummy007)
          (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
            (Wff.classEq (Class.cv (nb064AlphaDummy007))
              (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy007)
          (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
            (Wff.classEq (Class.cv (nb064AlphaDummy007))
              (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_038`. -/
@[expose]
noncomputable def nb064AlphaDummy038 (r : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb064AlphaDummy009 r a)
          (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
              (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy009 r a)
          (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
            (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
              (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_039`. -/
@[expose]
noncomputable def nb064AlphaDummy039 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb064AlphaDummy008))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_040`. -/
@[expose]
noncomputable def nb064AlphaDummy040 (r : Var) (a : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb064AlphaDummy010 r a))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_041`. -/
@[expose]
noncomputable def nb064AlphaDummy041 : Var :=
  (freshVar (((synCphi (Class.cv (nb064AlphaDummy008)))).fv ∪
      ((synCphi (Class.cv (nb064AlphaDummy008)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_042`. -/
@[expose]
noncomputable def nb064AlphaDummy042 (r : Var) (a : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb064AlphaDummy010 r a)))).fv ∪
      ((synCphi (Class.cv (nb064AlphaDummy010 r a)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_043`. -/
@[expose]
noncomputable def nb064AlphaDummy043 : Var :=
  (freshVar (((synCnin (Class.cv (nb064AlphaDummy002))
          (Class.cv (nb064AlphaDummy000)))).fv ∪
      ((synCnin (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_044`. -/
@[expose]
noncomputable def nb064AlphaDummy044 (x : Var) (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv x) (Class.cv a))).fv ∪
      ((synCnin (Class.cv x) (Class.cv a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_045`. -/
@[expose]
noncomputable def nb064AlphaDummy045 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy002))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_046`. -/
@[expose]
noncomputable def nb064AlphaDummy046 (x : Var) (a : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_047`. -/
@[expose]
noncomputable def nb064AlphaDummy047 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_048`. -/
@[expose]
noncomputable def nb064AlphaDummy048 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_049`. -/
@[expose]
noncomputable def nb064AlphaDummy049 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_050`. -/
@[expose]
noncomputable def nb064AlphaDummy050 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_051`. -/
@[expose]
noncomputable def nb064AlphaDummy051 : Var :=
  (freshVar (((synCcompl (Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCphi (Class.cv (nb064AlphaDummy048)))))))).fv ∪ ((synCcompl
          (Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_052`. -/
@[expose]
noncomputable def nb064AlphaDummy052 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCphi (Class.cv (nb064AlphaDummy050 y z)))))))).fv ∪ ((synCcompl
          (Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_053`. -/
@[expose]
noncomputable def nb064AlphaDummy053 : Var :=
  (freshVar (((Class.cab (nb064AlphaDummy047)
          (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
            (Wff.classEq (Class.cv (nb064AlphaDummy047))
              (synCphi (Class.cv (nb064AlphaDummy048))))))).fv ∪
      ((Class.cab (nb064AlphaDummy047)
          (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
            (Wff.classEq (Class.cv (nb064AlphaDummy047))
              (synCphi (Class.cv (nb064AlphaDummy048))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_054`. -/
@[expose]
noncomputable def nb064AlphaDummy054 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb064AlphaDummy049 y z)
          (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
            (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
              (synCphi (Class.cv (nb064AlphaDummy050 y z))))))).fv ∪
      ((Class.cab (nb064AlphaDummy049 y z) (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
            (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
              (synCphi (Class.cv (nb064AlphaDummy050 y z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_055`. -/
@[expose]
noncomputable def nb064AlphaDummy055 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy048))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_056`. -/
@[expose]
noncomputable def nb064AlphaDummy056 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy048))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_057`. -/
@[expose]
noncomputable def nb064AlphaDummy057 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy050 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_058`. -/
@[expose]
noncomputable def nb064AlphaDummy058 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy050 y z))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_059`. -/
@[expose]
noncomputable def nb064AlphaDummy059 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb064AlphaDummy055)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb064AlphaDummy055)) (synC1c))).fv ∪
      ((Class.cv (nb064AlphaDummy055))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_060`. -/
@[expose]
noncomputable def nb064AlphaDummy060 (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb064AlphaDummy057 y z)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb064AlphaDummy057 y z)) (synC1c))).fv ∪
      ((Class.cv (nb064AlphaDummy057 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_061`. -/
@[expose]
noncomputable def nb064AlphaDummy061 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_062`. -/
@[expose]
noncomputable def nb064AlphaDummy062 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_063`. -/
@[expose]
noncomputable def nb064AlphaDummy063 : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_064`. -/
@[expose]
noncomputable def nb064AlphaDummy064 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_065`. -/
@[expose]
noncomputable def nb064AlphaDummy065 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_066`. -/
@[expose]
noncomputable def nb064AlphaDummy066 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_067`. -/
@[expose]
noncomputable def nb064AlphaDummy067 : Var :=
  (freshVar (((synCnin (Class.cv (nb064AlphaDummy062))
          (Class.cv (nb064AlphaDummy063)))).fv ∪
      ((synCnin (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_068`. -/
@[expose]
noncomputable def nb064AlphaDummy068 (y : Var) (z : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb064AlphaDummy065 y z))
          (Class.cv (nb064AlphaDummy066 y z)))).fv ∪
      ((synCnin (Class.cv (nb064AlphaDummy065 y z))
          (Class.cv (nb064AlphaDummy066 y z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_069`. -/
@[expose]
noncomputable def nb064AlphaDummy069 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_070`. -/
@[expose]
noncomputable def nb064AlphaDummy070 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
      ((Class.cv (nb064AlphaDummy066 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_071`. -/
@[expose]
noncomputable def nb064AlphaDummy071 : Var :=
  (freshVar (((synCcompl (Class.cv (nb064AlphaDummy062)))).fv ∪
      ((synCcompl (Class.cv (nb064AlphaDummy063)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_072`. -/
@[expose]
noncomputable def nb064AlphaDummy072 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb064AlphaDummy065 y z)))).fv ∪
      ((synCcompl (Class.cv (nb064AlphaDummy066 y z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_073`. -/
@[expose]
noncomputable def nb064AlphaDummy073 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy062))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_074`. -/
@[expose]
noncomputable def nb064AlphaDummy074 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
      ((Class.cv (nb064AlphaDummy065 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_075`. -/
@[expose]
noncomputable def nb064AlphaDummy075 : Var :=
  (freshVar
    (((Class.cv (nb064AlphaDummy063))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_076`. -/
@[expose]
noncomputable def nb064AlphaDummy076 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (nb064AlphaDummy066 y z))).fv ∪
      ((Class.cv (nb064AlphaDummy066 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_077`. -/
@[expose]
noncomputable def nb064AlphaDummy077 : Var :=
  (freshVar (((Class.cab (nb064AlphaDummy047)
          (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
            (Wff.classEq (Class.cv (nb064AlphaDummy047))
              (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy047)
          (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
            (Wff.classEq (Class.cv (nb064AlphaDummy047))
              (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_078`. -/
@[expose]
noncomputable def nb064AlphaDummy078 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (nb064AlphaDummy049 y z)
          (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
              (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy049 y z)
          (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
            (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
              (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_079`. -/
@[expose]
noncomputable def nb064AlphaDummy079 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb064AlphaDummy048))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_080`. -/
@[expose]
noncomputable def nb064AlphaDummy080 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb064AlphaDummy050 y z))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_081`. -/
@[expose]
noncomputable def nb064AlphaDummy081 : Var :=
  (freshVar (((synCphi (Class.cv (nb064AlphaDummy048)))).fv ∪
      ((synCphi (Class.cv (nb064AlphaDummy048)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb064_alpha_dummy_082`. -/
@[expose]
noncomputable def nb064AlphaDummy082 (y : Var) (z : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb064AlphaDummy050 y z)))).fv ∪
      ((synCphi (Class.cv (nb064AlphaDummy050 y z)))).fv) 0)

theorem nb064_fresh_000 :
    (nb064AlphaDummy037) ∉
      (((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb064AlphaDummy037] using
    freshVar_not_mem
      (((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb064_fresh_001 :
    (nb064AlphaDummy013) ∉
      (((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCphi (Class.cv (nb064AlphaDummy008))))))).fv ∪
        ((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCphi (Class.cv (nb064AlphaDummy008))))))).fv) :=
  by
  simpa only [nb064AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCphi (Class.cv (nb064AlphaDummy008))))))).fv ∪
        ((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCphi (Class.cv (nb064AlphaDummy008))))))).fv)
      0

theorem nb064_fresh_002 (r : Var) (a : Var) :
    (nb064AlphaDummy038 r a) ∉
      (((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb064AlphaDummy038] using
    freshVar_not_mem
      (((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb064_fresh_003 (r : Var) (a : Var) :
    (nb064AlphaDummy014 r a) ∉
      (((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCphi (Class.cv (nb064AlphaDummy010 r a))))))).fv ∪
        ((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCphi (Class.cv (nb064AlphaDummy010 r a))))))).fv) :=
  by
  simpa only [nb064AlphaDummy014] using
    freshVar_not_mem
      (((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCphi (Class.cv (nb064AlphaDummy010 r a))))))).fv ∪
        ((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCphi (Class.cv (nb064AlphaDummy010 r a))))))).fv)
      0

theorem nb064_fresh_004 :
    (nb064AlphaDummy053) ∉
      (((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCphi (Class.cv (nb064AlphaDummy048))))))).fv ∪
        ((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCphi (Class.cv (nb064AlphaDummy048))))))).fv) :=
  by
  simpa only [nb064AlphaDummy053] using
    freshVar_not_mem
      (((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCphi (Class.cv (nb064AlphaDummy048))))))).fv ∪
        ((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCphi (Class.cv (nb064AlphaDummy048))))))).fv)
      0

theorem nb064_fresh_005 :
    (nb064AlphaDummy077) ∉
      (((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb064AlphaDummy077] using
    freshVar_not_mem
      (((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb064_fresh_006 (y : Var) (z : Var) :
    (nb064AlphaDummy054 y z) ∉
      (((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCphi (Class.cv (nb064AlphaDummy050 y z))))))).fv ∪
        ((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCphi (Class.cv (nb064AlphaDummy050 y z))))))).fv) :=
  by
  simpa only [nb064AlphaDummy054] using
    freshVar_not_mem
      (((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCphi (Class.cv (nb064AlphaDummy050 y z))))))).fv ∪
        ((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCphi (Class.cv (nb064AlphaDummy050 y z))))))).fv)
      0

theorem nb064_fresh_007 (y : Var) (z : Var) :
    (nb064AlphaDummy078 y z) ∉
      (((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb064AlphaDummy078] using
    freshVar_not_mem
      (((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb064_fresh_008 :
    (nb064AlphaDummy007) ∉
      (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) :=
  by
  simpa only [nb064AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv)
      0

theorem nb064_fresh_009 :
    (nb064AlphaDummy008) ∉
      (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) :=
  by
  simpa only [nb064AlphaDummy008] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv)
      1

theorem nb064_distinct_010 : (nb064AlphaDummy007) ≠ (nb064AlphaDummy008) := by
  simpa only [nb064AlphaDummy007, nb064AlphaDummy008] using
    (freshVar_injective
      (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb064_fresh_011 :
    (nb064AlphaDummy045) ∉
      (((Class.cv (nb064AlphaDummy002))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) :=
  by
  simpa only [nb064AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy002))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv)
      0

theorem nb064_fresh_012 :
    (nb064AlphaDummy047) ∉
      (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv) :=
  by
  simpa only [nb064AlphaDummy047] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv)
      0

theorem nb064_fresh_013 :
    (nb064AlphaDummy048) ∉
      (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv) :=
  by
  simpa only [nb064AlphaDummy048] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv)
      1

theorem nb064_distinct_014 : (nb064AlphaDummy047) ≠ (nb064AlphaDummy048) := by
  simpa only [nb064AlphaDummy047, nb064AlphaDummy048] using
    (freshVar_injective
      (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb064_fresh_015 :
    (nb064AlphaDummy015) ∉ (((Class.cv (nb064AlphaDummy008))).fv) := by
  simpa only [nb064AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy008))).fv) 0

theorem nb064_fresh_016 :
    (nb064AlphaDummy016) ∉ (((Class.cv (nb064AlphaDummy008))).fv) := by
  simpa only [nb064AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy008))).fv) 1

theorem nb064_distinct_017 : (nb064AlphaDummy015) ≠ (nb064AlphaDummy016) := by
  simpa only [nb064AlphaDummy015, nb064AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy008))).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_018 (r : Var) (a : Var) :
    (nb064AlphaDummy017 r a) ∉ (((Class.cv (nb064AlphaDummy010 r a))).fv) := by
  simpa only [nb064AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy010 r a))).fv) 0

theorem nb064_fresh_019 (r : Var) (a : Var) :
    (nb064AlphaDummy018 r a) ∉ (((Class.cv (nb064AlphaDummy010 r a))).fv) := by
  simpa only [nb064AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy010 r a))).fv) 1

theorem nb064_distinct_020 (r : Var) (a : Var) :
    (nb064AlphaDummy017 r a) ≠ (nb064AlphaDummy018 r a) := by
  simpa only [nb064AlphaDummy017, nb064AlphaDummy018] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy010 r a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb064_fresh_021 :
    (nb064AlphaDummy021) ∉
      (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) 0

theorem nb064_fresh_022 :
    (nb064AlphaDummy022) ∉
      (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) 1

theorem nb064_fresh_023 :
    (nb064AlphaDummy023) ∉
      (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) 2

theorem nb064_distinct_024 : (nb064AlphaDummy021) ≠ (nb064AlphaDummy022) := by
  simpa only [nb064AlphaDummy021, nb064AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb064_distinct_025 : (nb064AlphaDummy021) ≠ (nb064AlphaDummy023) := by
  simpa only [nb064AlphaDummy021, nb064AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb064_distinct_026 : (nb064AlphaDummy022) ≠ (nb064AlphaDummy023) := by
  simpa only [nb064AlphaDummy022, nb064AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb064_fresh_027 (r : Var) (a : Var) :
    (nb064AlphaDummy024 r a) ∉
      (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 0

theorem nb064_fresh_028 (r : Var) (a : Var) :
    (nb064AlphaDummy025 r a) ∉
      (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 1

theorem nb064_fresh_029 (r : Var) (a : Var) :
    (nb064AlphaDummy026 r a) ∉
      (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) 2

theorem nb064_distinct_030 (r : Var) (a : Var) :
    (nb064AlphaDummy024 r a) ≠ (nb064AlphaDummy025 r a) := by
  simpa only [nb064AlphaDummy024, nb064AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb064_distinct_031 (r : Var) (a : Var) :
    (nb064AlphaDummy024 r a) ≠ (nb064AlphaDummy026 r a) := by
  simpa only [nb064AlphaDummy024, nb064AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb064_distinct_032 (r : Var) (a : Var) :
    (nb064AlphaDummy025 r a) ≠ (nb064AlphaDummy026 r a) := by
  simpa only [nb064AlphaDummy025, nb064AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb064_fresh_033 :
    (nb064AlphaDummy033) ∉
      (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy022))).fv) :=
  by
  simpa only [nb064AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy022))).fv)
      0

theorem nb064_fresh_034 :
    (nb064AlphaDummy029) ∉
      (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv) :=
  by
  simpa only [nb064AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv)
      0

theorem nb064_fresh_035 :
    (nb064AlphaDummy035) ∉
      (((Class.cv (nb064AlphaDummy023))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv) :=
  by
  simpa only [nb064AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy023))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv)
      0

theorem nb064_fresh_036 (r : Var) (a : Var) :
    (nb064AlphaDummy034 r a) ∉
      (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy025 r a))).fv) :=
  by
  simpa only [nb064AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy025 r a))).fv)
      0

theorem nb064_fresh_037 (r : Var) (a : Var) :
    (nb064AlphaDummy030 r a) ∉
      (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy026 r a))).fv) :=
  by
  simpa only [nb064AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy026 r a))).fv)
      0

theorem nb064_fresh_038 (r : Var) (a : Var) :
    (nb064AlphaDummy036 r a) ∉
      (((Class.cv (nb064AlphaDummy026 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy026 r a))).fv) :=
  by
  simpa only [nb064AlphaDummy036] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy026 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy026 r a))).fv)
      0

theorem nb064_fresh_039 :
    (nb064AlphaDummy055) ∉ (((Class.cv (nb064AlphaDummy048))).fv) := by
  simpa only [nb064AlphaDummy055] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy048))).fv) 0

theorem nb064_fresh_040 :
    (nb064AlphaDummy056) ∉ (((Class.cv (nb064AlphaDummy048))).fv) := by
  simpa only [nb064AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy048))).fv) 1

theorem nb064_distinct_041 : (nb064AlphaDummy055) ≠ (nb064AlphaDummy056) := by
  simpa only [nb064AlphaDummy055, nb064AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy048))).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_042 (y : Var) (z : Var) :
    (nb064AlphaDummy057 y z) ∉ (((Class.cv (nb064AlphaDummy050 y z))).fv) := by
  simpa only [nb064AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy050 y z))).fv) 0

theorem nb064_fresh_043 (y : Var) (z : Var) :
    (nb064AlphaDummy058 y z) ∉ (((Class.cv (nb064AlphaDummy050 y z))).fv) := by
  simpa only [nb064AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy050 y z))).fv) 1

theorem nb064_distinct_044 (y : Var) (z : Var) :
    (nb064AlphaDummy057 y z) ≠ (nb064AlphaDummy058 y z) := by
  simpa only [nb064AlphaDummy057, nb064AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy050 y z))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb064_fresh_045 :
    (nb064AlphaDummy061) ∉
      (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) 0

theorem nb064_fresh_046 :
    (nb064AlphaDummy062) ∉
      (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) 1

theorem nb064_fresh_047 :
    (nb064AlphaDummy063) ∉
      (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) 2

theorem nb064_distinct_048 : (nb064AlphaDummy061) ≠ (nb064AlphaDummy062) := by
  simpa only [nb064AlphaDummy061, nb064AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb064_distinct_049 : (nb064AlphaDummy061) ≠ (nb064AlphaDummy063) := by
  simpa only [nb064AlphaDummy061, nb064AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb064_distinct_050 : (nb064AlphaDummy062) ≠ (nb064AlphaDummy063) := by
  simpa only [nb064AlphaDummy062, nb064AlphaDummy063] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb064_fresh_051 (y : Var) (z : Var) :
    (nb064AlphaDummy064 y z) ∉
      (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) 0

theorem nb064_fresh_052 (y : Var) (z : Var) :
    (nb064AlphaDummy065 y z) ∉
      (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy065] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) 1

theorem nb064_fresh_053 (y : Var) (z : Var) :
    (nb064AlphaDummy066 y z) ∉
      (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb064AlphaDummy066] using
    freshVar_not_mem (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) 2

theorem nb064_distinct_054 (y : Var) (z : Var) :
    (nb064AlphaDummy064 y z) ≠ (nb064AlphaDummy065 y z) := by
  simpa only [nb064AlphaDummy064, nb064AlphaDummy065] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb064_distinct_055 (y : Var) (z : Var) :
    (nb064AlphaDummy064 y z) ≠ (nb064AlphaDummy066 y z) := by
  simpa only [nb064AlphaDummy064, nb064AlphaDummy066] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb064_distinct_056 (y : Var) (z : Var) :
    (nb064AlphaDummy065 y z) ≠ (nb064AlphaDummy066 y z) := by
  simpa only [nb064AlphaDummy065, nb064AlphaDummy066] using
    (freshVar_injective (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb064_fresh_057 :
    (nb064AlphaDummy073) ∉
      (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy062))).fv) :=
  by
  simpa only [nb064AlphaDummy073] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy062))).fv)
      0

theorem nb064_fresh_058 :
    (nb064AlphaDummy069) ∉
      (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv) :=
  by
  simpa only [nb064AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv)
      0

theorem nb064_fresh_059 :
    (nb064AlphaDummy075) ∉
      (((Class.cv (nb064AlphaDummy063))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv) :=
  by
  simpa only [nb064AlphaDummy075] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy063))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv)
      0

theorem nb064_fresh_060 (y : Var) (z : Var) :
    (nb064AlphaDummy074 y z) ∉
      (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy065 y z))).fv) :=
  by
  simpa only [nb064AlphaDummy074] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy065 y z))).fv)
      0

theorem nb064_fresh_061 (y : Var) (z : Var) :
    (nb064AlphaDummy070 y z) ∉
      (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy066 y z))).fv) :=
  by
  simpa only [nb064AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy066 y z))).fv)
      0

theorem nb064_fresh_062 (y : Var) (z : Var) :
    (nb064AlphaDummy076 y z) ∉
      (((Class.cv (nb064AlphaDummy066 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy066 y z))).fv) :=
  by
  simpa only [nb064AlphaDummy076] using
    freshVar_not_mem
      (((Class.cv (nb064AlphaDummy066 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy066 y z))).fv)
      0

theorem nb064_fresh_063 (r : Var) (a : Var) :
    (nb064AlphaDummy009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb064AlphaDummy009] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb064_fresh_064 (r : Var) (a : Var) :
    (nb064AlphaDummy010 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb064AlphaDummy010] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb064_distinct_065 (r : Var) (a : Var) :
    (nb064AlphaDummy009 r a) ≠ (nb064AlphaDummy010 r a) := by
  simpa only [nb064AlphaDummy009, nb064AlphaDummy010] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_066 (x : Var) (a : Var) :
    (nb064AlphaDummy046 x a) ∉ (((Class.cv x)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb064AlphaDummy046] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv a)).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C064C001Part002`. -/


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

theorem nb064_fresh_067 (y : Var) (z : Var) :
    (nb064AlphaDummy049 y z) ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb064AlphaDummy049] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0

theorem nb064_fresh_068 (y : Var) (z : Var) :
    (nb064AlphaDummy050 y z) ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb064AlphaDummy050] using
    freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1

theorem nb064_distinct_069 (y : Var) (z : Var) :
    (nb064AlphaDummy049 y z) ≠ (nb064AlphaDummy050 y z) := by
  simpa only [nb064AlphaDummy049, nb064AlphaDummy050] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_070 :
    (nb064AlphaDummy019) ∉
      (((Wff.classMem (Class.cv (nb064AlphaDummy015)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy015)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy015))).fv) :=
  by
  simpa only [nb064AlphaDummy019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb064AlphaDummy015)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy015)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy015))).fv)
      0

theorem nb064_fresh_071 (r : Var) (a : Var) :
    (nb064AlphaDummy020 r a) ∉
      (((Wff.classMem (Class.cv (nb064AlphaDummy017 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy017 r a)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy017 r a))).fv) :=
  by
  simpa only [nb064AlphaDummy020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb064AlphaDummy017 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy017 r a)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy017 r a))).fv)
      0

theorem nb064_fresh_072 :
    (nb064AlphaDummy059) ∉
      (((Wff.classMem (Class.cv (nb064AlphaDummy055)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy055)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy055))).fv) :=
  by
  simpa only [nb064AlphaDummy059] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb064AlphaDummy055)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy055)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy055))).fv)
      0

theorem nb064_fresh_073 (y : Var) (z : Var) :
    (nb064AlphaDummy060 y z) ∉
      (((Wff.classMem (Class.cv (nb064AlphaDummy057 y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy057 y z)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy057 y z))).fv) :=
  by
  simpa only [nb064AlphaDummy060] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb064AlphaDummy057 y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy057 y z)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy057 y z))).fv)
      0

theorem nb064_fresh_074 :
    (nb064AlphaDummy011) ∉
      (((synCcompl (Class.cab (nb064AlphaDummy007)
              (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
                (Wff.classEq (Class.cv (nb064AlphaDummy007))
                  (synCphi (Class.cv (nb064AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy007)
              (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
                (Wff.classEq (Class.cv (nb064AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb064AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb064AlphaDummy007)
              (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
                (Wff.classEq (Class.cv (nb064AlphaDummy007))
                  (synCphi (Class.cv (nb064AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy007)
              (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
                (Wff.classEq (Class.cv (nb064AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb064_fresh_075 (r : Var) (a : Var) :
    (nb064AlphaDummy012 r a) ∉
      (((synCcompl (Class.cab (nb064AlphaDummy009 r a)
              (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                  (synCphi (Class.cv (nb064AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy009 r a)
              (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb064AlphaDummy012] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb064AlphaDummy009 r a)
              (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                  (synCphi (Class.cv (nb064AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy009 r a)
              (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb064_fresh_076 :
    (nb064AlphaDummy051) ∉
      (((synCcompl (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCphi (Class.cv (nb064AlphaDummy048)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb064AlphaDummy051] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCphi (Class.cv (nb064AlphaDummy048)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb064_fresh_077 (y : Var) (z : Var) :
    (nb064AlphaDummy052 y z) ∉
      (((synCcompl (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCphi (Class.cv (nb064AlphaDummy050 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb064AlphaDummy052] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCphi (Class.cv (nb064AlphaDummy050 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb064_fresh_078 :
    (nb064AlphaDummy031) ∉
      (((synCcompl (Class.cv (nb064AlphaDummy022)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy023)))).fv) :=
  by
  simpa only [nb064AlphaDummy031] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb064AlphaDummy022)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy023)))).fv)
      0

theorem nb064_fresh_079 (r : Var) (a : Var) :
    (nb064AlphaDummy032 r a) ∉
      (((synCcompl (Class.cv (nb064AlphaDummy025 r a)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy026 r a)))).fv) :=
  by
  simpa only [nb064AlphaDummy032] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb064AlphaDummy025 r a)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy026 r a)))).fv)
      0

theorem nb064_fresh_080 :
    (nb064AlphaDummy071) ∉
      (((synCcompl (Class.cv (nb064AlphaDummy062)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy063)))).fv) :=
  by
  simpa only [nb064AlphaDummy071] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb064AlphaDummy062)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy063)))).fv)
      0

theorem nb064_fresh_081 (y : Var) (z : Var) :
    (nb064AlphaDummy072 y z) ∉
      (((synCcompl (Class.cv (nb064AlphaDummy065 y z)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy066 y z)))).fv) :=
  by
  simpa only [nb064AlphaDummy072] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb064AlphaDummy065 y z)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy066 y z)))).fv)
      0

theorem nb064_fresh_082 :
    (nb064AlphaDummy039) ∉
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb064AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb064_fresh_083 (r : Var) (a : Var) :
    (nb064AlphaDummy040 r a) ∉
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy010 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb064AlphaDummy040] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy010 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb064_fresh_084 :
    (nb064AlphaDummy079) ∉
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy048))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb064AlphaDummy079] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy048))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb064_fresh_085 (y : Var) (z : Var) :
    (nb064AlphaDummy080 y z) ∉
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy050 y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb064AlphaDummy080] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy050 y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb064_fresh_086 :
    (nb064AlphaDummy043) ∉
      (((synCnin (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy002))
            (Class.cv (nb064AlphaDummy000)))).fv) :=
  by
  simpa only [nb064AlphaDummy043] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))).fv)
      0

theorem nb064_fresh_087 :
    (nb064AlphaDummy027) ∉
      (((synCnin (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy022))
            (Class.cv (nb064AlphaDummy023)))).fv) :=
  by
  simpa only [nb064AlphaDummy027] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023)))).fv)
      0

theorem nb064_fresh_088 (r : Var) (a : Var) :
    (nb064AlphaDummy028 r a) ∉
      (((synCnin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a)))).fv) :=
  by
  simpa only [nb064AlphaDummy028] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a)))).fv)
      0

theorem nb064_fresh_089 :
    (nb064AlphaDummy067) ∉
      (((synCnin (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy062))
            (Class.cv (nb064AlphaDummy063)))).fv) :=
  by
  simpa only [nb064AlphaDummy067] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063)))).fv)
      0

theorem nb064_fresh_090 (y : Var) (z : Var) :
    (nb064AlphaDummy068 y z) ∉
      (((synCnin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z)))).fv) :=
  by
  simpa only [nb064AlphaDummy068] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z)))).fv)
      0

theorem nb064_fresh_091 (x : Var) (a : Var) :
    (nb064AlphaDummy044 x a) ∉
      (((synCnin (Class.cv x) (Class.cv a))).fv ∪ ((synCnin (Class.cv x) (Class.cv a))).fv) :=
  by
  simpa only [nb064AlphaDummy044] using
    freshVar_not_mem
      (((synCnin (Class.cv x) (Class.cv a))).fv ∪ ((synCnin (Class.cv x) (Class.cv a))).fv)
      0

theorem nb064_fresh_092 :
    (nb064AlphaDummy041) ∉
      (((synCphi (Class.cv (nb064AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy008)))).fv) :=
  by
  simpa only [nb064AlphaDummy041] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb064AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy008)))).fv)
      0

theorem nb064_fresh_093 (r : Var) (a : Var) :
    (nb064AlphaDummy042 r a) ∉
      (((synCphi (Class.cv (nb064AlphaDummy010 r a)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy010 r a)))).fv) :=
  by
  simpa only [nb064AlphaDummy042] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb064AlphaDummy010 r a)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy010 r a)))).fv)
      0

theorem nb064_fresh_094 :
    (nb064AlphaDummy081) ∉
      (((synCphi (Class.cv (nb064AlphaDummy048)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy048)))).fv) :=
  by
  simpa only [nb064AlphaDummy081] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb064AlphaDummy048)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy048)))).fv)
      0

theorem nb064_fresh_095 (y : Var) (z : Var) :
    (nb064AlphaDummy082 y z) ∉
      (((synCphi (Class.cv (nb064AlphaDummy050 y z)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy050 y z)))).fv) :=
  by
  simpa only [nb064AlphaDummy082] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb064AlphaDummy050 y z)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy050 y z)))).fv)
      0

theorem nb064_fresh_096 :
    (nb064AlphaDummy005) ∉
      (({(nb064AlphaDummy001)} : Finset Var) ∪ ({(nb064AlphaDummy000)} : Finset Var) ∪
        ((Wff.all (nb064AlphaDummy002) (Wff.imp (synWa
                (synWss (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))
                (synWne (Class.cv (nb064AlphaDummy002)) (synC0)))
              (synWrex (nb064AlphaDummy004) (Class.cv (nb064AlphaDummy002))
                (synWral (nb064AlphaDummy003) (Class.cv (nb064AlphaDummy002)) (Wff.imp
                    (synWbr (Class.cv (nb064AlphaDummy003))
                      (Class.cv (nb064AlphaDummy001)) (Class.cv (nb064AlphaDummy004)))
                    (Wff.objEq (nb064AlphaDummy003) (nb064AlphaDummy004)))))))).fv) :=
  by
  simpa only [nb064AlphaDummy005] using
    freshVar_not_mem
      (({(nb064AlphaDummy001)} : Finset Var) ∪ ({(nb064AlphaDummy000)} : Finset Var) ∪
        ((Wff.all (nb064AlphaDummy002) (Wff.imp (synWa
                (synWss (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))
                (synWne (Class.cv (nb064AlphaDummy002)) (synC0)))
              (synWrex (nb064AlphaDummy004) (Class.cv (nb064AlphaDummy002))
                (synWral (nb064AlphaDummy003) (Class.cv (nb064AlphaDummy002)) (Wff.imp
                    (synWbr (Class.cv (nb064AlphaDummy003))
                      (Class.cv (nb064AlphaDummy001)) (Class.cv (nb064AlphaDummy004)))
                    (Wff.objEq (nb064AlphaDummy003) (nb064AlphaDummy004)))))))).fv)
      0

theorem nb064_fresh_097 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    (nb064AlphaDummy006 x y z r a) ∉
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((Wff.all x (Wff.imp
              (synWa (synWss (Class.cv x) (Class.cv a)) (synWne (Class.cv x) (synC0)))
              (synWrex z (Class.cv x) (synWral y (Class.cv x)
                  (Wff.imp (synWbr (Class.cv y) (Class.cv r) (Class.cv z))
                    (Wff.objEq y z))))))).fv) :=
  by
  simpa only [nb064AlphaDummy006] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((Wff.all x (Wff.imp
              (synWa (synWss (Class.cv x) (Class.cv a)) (synWne (Class.cv x) (synC0)))
              (synWrex z (Class.cv x) (synWral y (Class.cv x)
                  (Wff.imp (synWbr (Class.cv y) (Class.cv r) (Class.cv z))
                    (Wff.objEq y z))))))).fv)
      0

theorem nb064_fresh_098 : (nb064AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb064AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb064_fresh_099 : (nb064AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb064AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb064_fresh_100 : (nb064AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb064AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb064_fresh_101 : (nb064AlphaDummy003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb064AlphaDummy003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb064_fresh_102 : (nb064AlphaDummy004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb064AlphaDummy004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb064_distinct_103 : (nb064AlphaDummy000) ≠ (nb064AlphaDummy001) := by
  simpa only [nb064AlphaDummy000, nb064AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb064_distinct_104 : (nb064AlphaDummy000) ≠ (nb064AlphaDummy002) := by
  simpa only [nb064AlphaDummy000, nb064AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb064_distinct_105 : (nb064AlphaDummy000) ≠ (nb064AlphaDummy003) := by
  simpa only [nb064AlphaDummy000, nb064AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb064_distinct_106 : (nb064AlphaDummy000) ≠ (nb064AlphaDummy004) := by
  simpa only [nb064AlphaDummy000, nb064AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb064_distinct_107 : (nb064AlphaDummy001) ≠ (nb064AlphaDummy002) := by
  simpa only [nb064AlphaDummy001, nb064AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb064_distinct_108 : (nb064AlphaDummy001) ≠ (nb064AlphaDummy003) := by
  simpa only [nb064AlphaDummy001, nb064AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb064_distinct_109 : (nb064AlphaDummy001) ≠ (nb064AlphaDummy004) := by
  simpa only [nb064AlphaDummy001, nb064AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb064_distinct_110 : (nb064AlphaDummy002) ≠ (nb064AlphaDummy003) := by
  simpa only [nb064AlphaDummy002, nb064AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb064_distinct_111 : (nb064AlphaDummy002) ≠ (nb064AlphaDummy004) := by
  simpa only [nb064AlphaDummy002, nb064AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb064_distinct_112 : (nb064AlphaDummy003) ≠ (nb064AlphaDummy004) := by
  simpa only [nb064AlphaDummy003, nb064AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb064_support_mem_0000 :
    (nb064AlphaDummy001) ∈
      (({(nb064AlphaDummy001)} : Finset Var) ∪ ({(nb064AlphaDummy000)} : Finset Var) ∪
        ((Wff.all (nb064AlphaDummy002) (Wff.imp (synWa
                (synWss (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))
                (synWne (Class.cv (nb064AlphaDummy002)) (synC0)))
              (synWrex (nb064AlphaDummy004) (Class.cv (nb064AlphaDummy002))
                (synWral (nb064AlphaDummy003) (Class.cv (nb064AlphaDummy002)) (Wff.imp
                    (synWbr (Class.cv (nb064AlphaDummy003))
                      (Class.cv (nb064AlphaDummy001)) (Class.cv (nb064AlphaDummy004)))
                    (Wff.objEq (nb064AlphaDummy003) (nb064AlphaDummy004)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((Wff.all x (Wff.imp
              (synWa (synWss (Class.cv x) (Class.cv a)) (synWne (Class.cv x) (synC0)))
              (synWrex z (Class.cv x) (synWral y (Class.cv x)
                  (Wff.imp (synWbr (Class.cv y) (Class.cv r) (Class.cv z))
                    (Wff.objEq y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0002 :
    (nb064AlphaDummy000) ∈
      (({(nb064AlphaDummy001)} : Finset Var) ∪ ({(nb064AlphaDummy000)} : Finset Var) ∪
        ((Wff.all (nb064AlphaDummy002) (Wff.imp (synWa
                (synWss (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))
                (synWne (Class.cv (nb064AlphaDummy002)) (synC0)))
              (synWrex (nb064AlphaDummy004) (Class.cv (nb064AlphaDummy002))
                (synWral (nb064AlphaDummy003) (Class.cv (nb064AlphaDummy002)) (Wff.imp
                    (synWbr (Class.cv (nb064AlphaDummy003))
                      (Class.cv (nb064AlphaDummy001)) (Class.cv (nb064AlphaDummy004)))
                    (Wff.objEq (nb064AlphaDummy003) (nb064AlphaDummy004)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0003 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) :
    a ∈
      (({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((Wff.all x (Wff.imp
              (synWa (synWss (Class.cv x) (Class.cv a)) (synWne (Class.cv x) (synC0)))
              (synWrex z (Class.cv x) (synWral y (Class.cv x)
                  (Wff.imp (synWbr (Class.cv y) (Class.cv r) (Class.cv z))
                    (Wff.objEq y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0004 :
    (nb064AlphaDummy001) ∈
      (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0005 :
    (nb064AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb064AlphaDummy007)
              (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
                (Wff.classEq (Class.cv (nb064AlphaDummy007))
                  (synCphi (Class.cv (nb064AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy007)
              (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
                (Wff.classEq (Class.cv (nb064AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0006 (r : Var) (a : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0007 (r : Var) (a : Var) :
    r ∈
      (((synCcompl (Class.cab (nb064AlphaDummy009 r a)
              (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                  (synCphi (Class.cv (nb064AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy009 r a)
              (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0008 :
    (nb064AlphaDummy001) ∈
      (((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCphi (Class.cv (nb064AlphaDummy008))))))).fv ∪
        ((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCphi (Class.cv (nb064AlphaDummy008))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0009 (r : Var) (a : Var) :
    r ∈
      (((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCphi (Class.cv (nb064AlphaDummy010 r a))))))).fv ∪
        ((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCphi (Class.cv (nb064AlphaDummy010 r a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0010 :
    (nb064AlphaDummy008) ∈ (((Class.cv (nb064AlphaDummy008))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0011 (r : Var) (a : Var) :
    (nb064AlphaDummy010 r a) ∈ (((Class.cv (nb064AlphaDummy010 r a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0012 :
    (nb064AlphaDummy015) ∈
      (((Wff.classMem (Class.cv (nb064AlphaDummy015)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy015)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy015))).fv) :=
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

theorem nb064_support_mem_0013 (r : Var) (a : Var) :
    (nb064AlphaDummy017 r a) ∈
      (((Wff.classMem (Class.cv (nb064AlphaDummy017 r a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy017 r a)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy017 r a))).fv) :=
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

theorem nb064_support_mem_0014 :
    (nb064AlphaDummy015) ∈
      (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0015 (r : Var) (a : Var) :
    (nb064AlphaDummy017 r a) ∈
      (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0016 :
    (nb064AlphaDummy022) ∈
      (((synCnin (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy022))
            (Class.cv (nb064AlphaDummy023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0017 (r : Var) (a : Var) :
    (nb064AlphaDummy025 r a) ∈
      (((synCnin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0018 :
    (nb064AlphaDummy022) ∈
      (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0019 (r : Var) (a : Var) :
    (nb064AlphaDummy025 r a) ∈
      (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0020 :
    (nb064AlphaDummy023) ∈
      (((synCnin (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy022))
            (Class.cv (nb064AlphaDummy023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0021 (r : Var) (a : Var) :
    (nb064AlphaDummy026 r a) ∈
      (((synCnin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0022 :
    (nb064AlphaDummy023) ∈
      (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0023 (r : Var) (a : Var) :
    (nb064AlphaDummy026 r a) ∈
      (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0024 :
    (nb064AlphaDummy022) ∈
      (((synCcompl (Class.cv (nb064AlphaDummy022)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0025 (r : Var) (a : Var) :
    (nb064AlphaDummy025 r a) ∈
      (((synCcompl (Class.cv (nb064AlphaDummy025 r a)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0026 :
    (nb064AlphaDummy022) ∈
      (((Class.cv (nb064AlphaDummy022))).fv ∪ ((Class.cv (nb064AlphaDummy022))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0027 (r : Var) (a : Var) :
    (nb064AlphaDummy025 r a) ∈
      (((Class.cv (nb064AlphaDummy025 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy025 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0028 :
    (nb064AlphaDummy023) ∈
      (((synCcompl (Class.cv (nb064AlphaDummy022)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy023)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0029 (r : Var) (a : Var) :
    (nb064AlphaDummy026 r a) ∈
      (((synCcompl (Class.cv (nb064AlphaDummy025 r a)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy026 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0030 :
    (nb064AlphaDummy023) ∈
      (((Class.cv (nb064AlphaDummy023))).fv ∪ ((Class.cv (nb064AlphaDummy023))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0031 (r : Var) (a : Var) :
    (nb064AlphaDummy026 r a) ∈
      (((Class.cv (nb064AlphaDummy026 r a))).fv ∪
        ((Class.cv (nb064AlphaDummy026 r a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0032 :
    (nb064AlphaDummy000) ∈
      (((Class.cv (nb064AlphaDummy001))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0033 :
    (nb064AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb064AlphaDummy007)
              (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy001))
                (Wff.classEq (Class.cv (nb064AlphaDummy007))
                  (synCphi (Class.cv (nb064AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy007)
              (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
                (Wff.classEq (Class.cv (nb064AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0034 (r : Var) (a : Var) :
    a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0035 (r : Var) (a : Var) :
    a ∈
      (((synCcompl (Class.cab (nb064AlphaDummy009 r a)
              (synWrex (nb064AlphaDummy010 r a) (Class.cv r)
                (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                  (synCphi (Class.cv (nb064AlphaDummy010 r a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy009 r a)
              (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
                (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0036 :
    (nb064AlphaDummy000) ∈
      (((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy007)
            (synWrex (nb064AlphaDummy008) (Class.cv (nb064AlphaDummy000))
              (Wff.classEq (Class.cv (nb064AlphaDummy007))
                (synCun (synCphi (Class.cv (nb064AlphaDummy008)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0037 (r : Var) (a : Var) :
    a ∈
      (((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy009 r a)
            (synWrex (nb064AlphaDummy010 r a) (Class.cv a)
              (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
                (synCun (synCphi (Class.cv (nb064AlphaDummy010 r a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0034 r a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0034 r a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0038 :
    (nb064AlphaDummy008) ∈
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0039 (r : Var) (a : Var) :
    (nb064AlphaDummy010 r a) ∈
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy010 r a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0040 :
    (nb064AlphaDummy008) ∈
      (((synCphi (Class.cv (nb064AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy008)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0041 (r : Var) (a : Var) :
    (nb064AlphaDummy010 r a) ∈
      (((synCphi (Class.cv (nb064AlphaDummy010 r a)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy010 r a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0042 :
    (nb064AlphaDummy002) ∈
      (((synCnin (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy002))
            (Class.cv (nb064AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0043 (x : Var) (a : Var) :
    x ∈
      (((synCnin (Class.cv x) (Class.cv a))).fv ∪ ((synCnin (Class.cv x) (Class.cv a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0044 :
    (nb064AlphaDummy002) ∈
      (((Class.cv (nb064AlphaDummy002))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0045 (x : Var) (a : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0046 :
    (nb064AlphaDummy000) ∈
      (((synCnin (Class.cv (nb064AlphaDummy002)) (Class.cv (nb064AlphaDummy000)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy002))
            (Class.cv (nb064AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0047 (x : Var) (a : Var) :
    a ∈
      (((synCnin (Class.cv x) (Class.cv a))).fv ∪ ((synCnin (Class.cv x) (Class.cv a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0048 :
    (nb064AlphaDummy000) ∈
      (((Class.cv (nb064AlphaDummy002))).fv ∪ ((Class.cv (nb064AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0049 (x : Var) (a : Var) :
    a ∈ (((Class.cv x)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0050 :
    (nb064AlphaDummy003) ∈
      (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0051 :
    (nb064AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCphi (Class.cv (nb064AlphaDummy048)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0052 (y : Var) (z : Var) :
    y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0053 (y : Var) (z : Var) :
    y ∈
      (((synCcompl (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCphi (Class.cv (nb064AlphaDummy050 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0052 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0052 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0054 :
    (nb064AlphaDummy003) ∈
      (((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCphi (Class.cv (nb064AlphaDummy048))))))).fv ∪
        ((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCphi (Class.cv (nb064AlphaDummy048))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0055 (y : Var) (z : Var) :
    y ∈
      (((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCphi (Class.cv (nb064AlphaDummy050 y z))))))).fv ∪
        ((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCphi (Class.cv (nb064AlphaDummy050 y z))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0052 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0052 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0056 :
    (nb064AlphaDummy048) ∈ (((Class.cv (nb064AlphaDummy048))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0057 (y : Var) (z : Var) :
    (nb064AlphaDummy050 y z) ∈ (((Class.cv (nb064AlphaDummy050 y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0058 :
    (nb064AlphaDummy055) ∈
      (((Wff.classMem (Class.cv (nb064AlphaDummy055)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy055)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy055))).fv) :=
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

theorem nb064_support_mem_0059 (y : Var) (z : Var) :
    (nb064AlphaDummy057 y z) ∈
      (((Wff.classMem (Class.cv (nb064AlphaDummy057 y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb064AlphaDummy057 y z)) (synC1c))).fv ∪
        ((Class.cv (nb064AlphaDummy057 y z))).fv) :=
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

theorem nb064_support_mem_0060 :
    (nb064AlphaDummy055) ∈
      (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0061 (y : Var) (z : Var) :
    (nb064AlphaDummy057 y z) ∈
      (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0062 :
    (nb064AlphaDummy062) ∈
      (((synCnin (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy062))
            (Class.cv (nb064AlphaDummy063)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0063 (y : Var) (z : Var) :
    (nb064AlphaDummy065 y z) ∈
      (((synCnin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0064 :
    (nb064AlphaDummy062) ∈
      (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0065 (y : Var) (z : Var) :
    (nb064AlphaDummy065 y z) ∈
      (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy066 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0066 :
    (nb064AlphaDummy063) ∈
      (((synCnin (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy062))
            (Class.cv (nb064AlphaDummy063)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0067 (y : Var) (z : Var) :
    (nb064AlphaDummy066 y z) ∈
      (((synCnin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z)))).fv ∪
        ((synCnin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0068 :
    (nb064AlphaDummy063) ∈
      (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0069 (y : Var) (z : Var) :
    (nb064AlphaDummy066 y z) ∈
      (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy066 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0070 :
    (nb064AlphaDummy062) ∈
      (((synCcompl (Class.cv (nb064AlphaDummy062)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy063)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0071 (y : Var) (z : Var) :
    (nb064AlphaDummy065 y z) ∈
      (((synCcompl (Class.cv (nb064AlphaDummy065 y z)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy066 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0072 :
    (nb064AlphaDummy062) ∈
      (((Class.cv (nb064AlphaDummy062))).fv ∪ ((Class.cv (nb064AlphaDummy062))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0073 (y : Var) (z : Var) :
    (nb064AlphaDummy065 y z) ∈
      (((Class.cv (nb064AlphaDummy065 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy065 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0074 :
    (nb064AlphaDummy063) ∈
      (((synCcompl (Class.cv (nb064AlphaDummy062)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy063)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0075 (y : Var) (z : Var) :
    (nb064AlphaDummy066 y z) ∈
      (((synCcompl (Class.cv (nb064AlphaDummy065 y z)))).fv ∪
        ((synCcompl (Class.cv (nb064AlphaDummy066 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0076 :
    (nb064AlphaDummy063) ∈
      (((Class.cv (nb064AlphaDummy063))).fv ∪ ((Class.cv (nb064AlphaDummy063))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0077 (y : Var) (z : Var) :
    (nb064AlphaDummy066 y z) ∈
      (((Class.cv (nb064AlphaDummy066 y z))).fv ∪
        ((Class.cv (nb064AlphaDummy066 y z))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0078 :
    (nb064AlphaDummy004) ∈
      (((Class.cv (nb064AlphaDummy003))).fv ∪ ((Class.cv (nb064AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0079 :
    (nb064AlphaDummy004) ∈
      (((synCcompl (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy003))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCphi (Class.cv (nb064AlphaDummy048)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0080 (y : Var) (z : Var) :
    z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0081 (y : Var) (z : Var) :
    z ∈
      (((synCcompl (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv y)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCphi (Class.cv (nb064AlphaDummy050 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0082 :
    (nb064AlphaDummy004) ∈
      (((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0083 (y : Var) (z : Var) :
    z ∈
      (((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb064_support_mem_0084 :
    (nb064AlphaDummy048) ∈
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy048))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0085 (y : Var) (z : Var) :
    (nb064AlphaDummy050 y z) ∈
      (((synCcompl (synCphi (Class.cv (nb064AlphaDummy050 y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0086 :
    (nb064AlphaDummy048) ∈
      (((synCphi (Class.cv (nb064AlphaDummy048)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy048)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb064_support_mem_0087 (y : Var) (z : Var) :
    (nb064AlphaDummy050 y z) ∈
      (((synCphi (Class.cv (nb064AlphaDummy050 y z)))).fv ∪
        ((synCphi (Class.cv (nb064AlphaDummy050 y z)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
