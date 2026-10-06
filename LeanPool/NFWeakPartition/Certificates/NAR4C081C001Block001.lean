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

/-! Certificates from `NAR4C081C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_000`. -/
@[expose]
noncomputable def nb081AlphaDummy000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_001`. -/
@[expose]
noncomputable def nb081AlphaDummy001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_002`. -/
@[expose]
noncomputable def nb081AlphaDummy002 (A : Class) : Var :=
  (freshVar (({(nb081AlphaDummy000 A)} : Finset Var) ∪
        ({(nb081AlphaDummy001 A)} : Finset Var) ∪ ((Wff.classMem
          (synCopk (Class.cv (nb081AlphaDummy000 A)) (Class.cv (nb081AlphaDummy001 A)))
          A)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_003`. -/
@[expose]
noncomputable def nb081AlphaDummy003 (x : Var) (y : Var) (A : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((Wff.classMem (synCopk (Class.cv x) (Class.cv y)) A)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_004`. -/
@[expose]
noncomputable def nb081AlphaDummy004 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy000 A))).fv ∪
      ((Class.cv (nb081AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_005`. -/
@[expose]
noncomputable def nb081AlphaDummy005 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy000 A))).fv ∪
      ((Class.cv (nb081AlphaDummy001 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_006`. -/
@[expose]
noncomputable def nb081AlphaDummy006 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_007`. -/
@[expose]
noncomputable def nb081AlphaDummy007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_008`. -/
@[expose]
noncomputable def nb081AlphaDummy008 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCphi (Class.cv (nb081AlphaDummy005 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_009`. -/
@[expose]
noncomputable def nb081AlphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCphi (Class.cv (nb081AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_010`. -/
@[expose]
noncomputable def nb081AlphaDummy010 (A : Class) : Var :=
  (freshVar (((Class.cab (nb081AlphaDummy004 A)
          (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
            (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
              (synCphi (Class.cv (nb081AlphaDummy005 A))))))).fv ∪
      ((Class.cab (nb081AlphaDummy004 A)
          (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
            (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
              (synCphi (Class.cv (nb081AlphaDummy005 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_011`. -/
@[expose]
noncomputable def nb081AlphaDummy011 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb081AlphaDummy006 x y)
          (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
              (synCphi (Class.cv (nb081AlphaDummy007 x y))))))).fv ∪
      ((Class.cab (nb081AlphaDummy006 x y) (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
              (synCphi (Class.cv (nb081AlphaDummy007 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_012`. -/
@[expose]
noncomputable def nb081AlphaDummy012 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy005 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_013`. -/
@[expose]
noncomputable def nb081AlphaDummy013 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy005 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_014`. -/
@[expose]
noncomputable def nb081AlphaDummy014 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy007 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_015`. -/
@[expose]
noncomputable def nb081AlphaDummy015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy007 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_016`. -/
@[expose]
noncomputable def nb081AlphaDummy016 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb081AlphaDummy012 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb081AlphaDummy012 A)) (synC1c))).fv ∪
      ((Class.cv (nb081AlphaDummy012 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_017`. -/
@[expose]
noncomputable def nb081AlphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb081AlphaDummy014 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb081AlphaDummy014 x y)) (synC1c))).fv ∪
      ((Class.cv (nb081AlphaDummy014 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_018`. -/
@[expose]
noncomputable def nb081AlphaDummy018 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_019`. -/
@[expose]
noncomputable def nb081AlphaDummy019 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_020`. -/
@[expose]
noncomputable def nb081AlphaDummy020 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_021`. -/
@[expose]
noncomputable def nb081AlphaDummy021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_022`. -/
@[expose]
noncomputable def nb081AlphaDummy022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_023`. -/
@[expose]
noncomputable def nb081AlphaDummy023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_024`. -/
@[expose]
noncomputable def nb081AlphaDummy024 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb081AlphaDummy019 A))
          (Class.cv (nb081AlphaDummy020 A)))).fv ∪
      ((synCnin (Class.cv (nb081AlphaDummy019 A)) (Class.cv (nb081AlphaDummy020 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_025`. -/
@[expose]
noncomputable def nb081AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb081AlphaDummy022 x y))
          (Class.cv (nb081AlphaDummy023 x y)))).fv ∪
      ((synCnin (Class.cv (nb081AlphaDummy022 x y))
          (Class.cv (nb081AlphaDummy023 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_026`. -/
@[expose]
noncomputable def nb081AlphaDummy026 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy019 A))).fv ∪
      ((Class.cv (nb081AlphaDummy020 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_027`. -/
@[expose]
noncomputable def nb081AlphaDummy027 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
      ((Class.cv (nb081AlphaDummy023 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_028`. -/
@[expose]
noncomputable def nb081AlphaDummy028 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb081AlphaDummy019 A)))).fv ∪
      ((synCcompl (Class.cv (nb081AlphaDummy020 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_029`. -/
@[expose]
noncomputable def nb081AlphaDummy029 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb081AlphaDummy022 x y)))).fv ∪
      ((synCcompl (Class.cv (nb081AlphaDummy023 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_030`. -/
@[expose]
noncomputable def nb081AlphaDummy030 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy019 A))).fv ∪
      ((Class.cv (nb081AlphaDummy019 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_031`. -/
@[expose]
noncomputable def nb081AlphaDummy031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
      ((Class.cv (nb081AlphaDummy022 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_032`. -/
@[expose]
noncomputable def nb081AlphaDummy032 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy020 A))).fv ∪
      ((Class.cv (nb081AlphaDummy020 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_033`. -/
@[expose]
noncomputable def nb081AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy023 x y))).fv ∪
      ((Class.cv (nb081AlphaDummy023 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_034`. -/
@[expose]
noncomputable def nb081AlphaDummy034 (A : Class) : Var :=
  (freshVar (((Class.cab (nb081AlphaDummy004 A)
          (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
              (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb081AlphaDummy004 A)
          (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
              (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_035`. -/
@[expose]
noncomputable def nb081AlphaDummy035 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb081AlphaDummy006 x y)
          (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
              (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb081AlphaDummy006 x y)
          (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
              (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_036`. -/
@[expose]
noncomputable def nb081AlphaDummy036 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb081AlphaDummy005 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_037`. -/
@[expose]
noncomputable def nb081AlphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb081AlphaDummy007 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_038`. -/
@[expose]
noncomputable def nb081AlphaDummy038 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb081AlphaDummy005 A)))).fv ∪
      ((synCphi (Class.cv (nb081AlphaDummy005 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_039`. -/
@[expose]
noncomputable def nb081AlphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb081AlphaDummy007 x y)))).fv ∪
      ((synCphi (Class.cv (nb081AlphaDummy007 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_040`. -/
@[expose]
noncomputable def nb081AlphaDummy040 (A : Class) : Var :=
  (freshVar (((synCcompl (synCsn (synCsn (Class.cv (nb081AlphaDummy000 A)))))).fv ∪
      ((synCcompl (synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_041`. -/
@[expose]
noncomputable def nb081AlphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCsn (synCsn (Class.cv x))))).fv ∪
      ((synCcompl (synCsn (synCpr (Class.cv x) (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_042`. -/
@[expose]
noncomputable def nb081AlphaDummy042 (A : Class) : Var :=
  (freshVar (((synCsn (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
      ((synCsn (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_043`. -/
@[expose]
noncomputable def nb081AlphaDummy043 (x : Var) : Var :=
  (freshVar (((synCsn (synCsn (Class.cv x)))).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_044`. -/
@[expose]
noncomputable def nb081AlphaDummy044 (A : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_045`. -/
@[expose]
noncomputable def nb081AlphaDummy045 (x : Var) : Var :=
  (freshVar (((synCsn (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_046`. -/
@[expose]
noncomputable def nb081AlphaDummy046 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy000 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_047`. -/
@[expose]
noncomputable def nb081AlphaDummy047 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_048`. -/
@[expose]
noncomputable def nb081AlphaDummy048 (A : Class) : Var :=
  (freshVar (((synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
            (Class.cv (nb081AlphaDummy001 A))))).fv ∪ ((synCsn
          (synCpr (Class.cv (nb081AlphaDummy000 A))
            (Class.cv (nb081AlphaDummy001 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_049`. -/
@[expose]
noncomputable def nb081AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv ∪
      ((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_050`. -/
@[expose]
noncomputable def nb081AlphaDummy050 (A : Class) : Var :=
  (freshVar (((synCpr (Class.cv (nb081AlphaDummy000 A))
        (Class.cv (nb081AlphaDummy001 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_051`. -/
@[expose]
noncomputable def nb081AlphaDummy051 (x : Var) (y : Var) : Var :=
  (freshVar (((synCpr (Class.cv x) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_052`. -/
@[expose]
noncomputable def nb081AlphaDummy052 (A : Class) : Var :=
  (freshVar (((synCcompl (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
      ((synCcompl (synCsn (Class.cv (nb081AlphaDummy001 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_053`. -/
@[expose]
noncomputable def nb081AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar
    (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_054`. -/
@[expose]
noncomputable def nb081AlphaDummy054 (A : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv ∪
      ((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_055`. -/
@[expose]
noncomputable def nb081AlphaDummy055 (x : Var) : Var :=
  (freshVar (((synCsn (Class.cv x))).fv ∪ ((synCsn (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_056`. -/
@[expose]
noncomputable def nb081AlphaDummy056 (A : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb081AlphaDummy001 A)))).fv ∪
      ((synCsn (Class.cv (nb081AlphaDummy001 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_057`. -/
@[expose]
noncomputable def nb081AlphaDummy057 (y : Var) : Var :=
  (freshVar (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_058`. -/
@[expose]
noncomputable def nb081AlphaDummy058 (A : Class) : Var :=
  (freshVar (((Class.cv (nb081AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb081_alpha_dummy_059`. -/
@[expose]
noncomputable def nb081AlphaDummy059 (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv) 0)

theorem nb081_fresh_000 (A : Class) :
    (nb081AlphaDummy010 A) ∉
      (((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCphi (Class.cv (nb081AlphaDummy005 A))))))).fv ∪
        ((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCphi (Class.cv (nb081AlphaDummy005 A))))))).fv) :=
  by
  simpa only [nb081AlphaDummy010] using
    freshVar_not_mem
      (((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCphi (Class.cv (nb081AlphaDummy005 A))))))).fv ∪
        ((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCphi (Class.cv (nb081AlphaDummy005 A))))))).fv)
      0

theorem nb081_fresh_001 (A : Class) :
    (nb081AlphaDummy034 A) ∉
      (((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb081AlphaDummy034] using
    freshVar_not_mem
      (((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb081_fresh_002 (x : Var) (y : Var) :
    (nb081AlphaDummy011 x y) ∉
      (((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCphi (Class.cv (nb081AlphaDummy007 x y))))))).fv ∪
        ((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCphi (Class.cv (nb081AlphaDummy007 x y))))))).fv) :=
  by
  simpa only [nb081AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCphi (Class.cv (nb081AlphaDummy007 x y))))))).fv ∪
        ((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCphi (Class.cv (nb081AlphaDummy007 x y))))))).fv)
      0

theorem nb081_fresh_003 (x : Var) (y : Var) :
    (nb081AlphaDummy035 x y) ∉
      (((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb081AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb081_fresh_004 (A : Class) :
    (nb081AlphaDummy046 A) ∉ (((Class.cv (nb081AlphaDummy000 A))).fv) := by
  simpa only [nb081AlphaDummy046] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy000 A))).fv) 0

theorem nb081_fresh_005 (A : Class) :
    (nb081AlphaDummy004 A) ∉
      (((Class.cv (nb081AlphaDummy000 A))).fv ∪ ((Class.cv (nb081AlphaDummy001 A))).fv) :=
  by
  simpa only [nb081AlphaDummy004] using
    freshVar_not_mem
      (((Class.cv (nb081AlphaDummy000 A))).fv ∪ ((Class.cv (nb081AlphaDummy001 A))).fv)
      0

theorem nb081_fresh_006 (A : Class) :
    (nb081AlphaDummy005 A) ∉
      (((Class.cv (nb081AlphaDummy000 A))).fv ∪ ((Class.cv (nb081AlphaDummy001 A))).fv) :=
  by
  simpa only [nb081AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb081AlphaDummy000 A))).fv ∪ ((Class.cv (nb081AlphaDummy001 A))).fv)
      1

theorem nb081_distinct_007 (A : Class) :
    (nb081AlphaDummy004 A) ≠ (nb081AlphaDummy005 A) := by
  simpa only [nb081AlphaDummy004, nb081AlphaDummy005] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy000 A))).fv ∪
        ((Class.cv (nb081AlphaDummy001 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb081_fresh_008 (A : Class) :
    (nb081AlphaDummy058 A) ∉ (((Class.cv (nb081AlphaDummy001 A))).fv) := by
  simpa only [nb081AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy001 A))).fv) 0

theorem nb081_fresh_009 (A : Class) :
    (nb081AlphaDummy012 A) ∉ (((Class.cv (nb081AlphaDummy005 A))).fv) := by
  simpa only [nb081AlphaDummy012] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy005 A))).fv) 0

theorem nb081_fresh_010 (A : Class) :
    (nb081AlphaDummy013 A) ∉ (((Class.cv (nb081AlphaDummy005 A))).fv) := by
  simpa only [nb081AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy005 A))).fv) 1

theorem nb081_distinct_011 (A : Class) :
    (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy013 A) := by
  simpa only [nb081AlphaDummy012, nb081AlphaDummy013] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy005 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb081_fresh_012 (x : Var) (y : Var) :
    (nb081AlphaDummy014 x y) ∉ (((Class.cv (nb081AlphaDummy007 x y))).fv) := by
  simpa only [nb081AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy007 x y))).fv) 0

theorem nb081_fresh_013 (x : Var) (y : Var) :
    (nb081AlphaDummy015 x y) ∉ (((Class.cv (nb081AlphaDummy007 x y))).fv) := by
  simpa only [nb081AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy007 x y))).fv) 1

theorem nb081_distinct_014 (x : Var) (y : Var) :
    (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy015 x y) := by
  simpa only [nb081AlphaDummy014, nb081AlphaDummy015] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy007 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb081_fresh_015 (A : Class) :
    (nb081AlphaDummy018 A) ∉
      (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb081AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) 0

theorem nb081_fresh_016 (A : Class) :
    (nb081AlphaDummy019 A) ∉
      (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb081AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) 1

theorem nb081_fresh_017 (A : Class) :
    (nb081AlphaDummy020 A) ∉
      (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb081AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) 2

theorem nb081_distinct_018 (A : Class) :
    (nb081AlphaDummy018 A) ≠ (nb081AlphaDummy019 A) := by
  simpa only [nb081AlphaDummy018, nb081AlphaDummy019] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb081_distinct_019 (A : Class) :
    (nb081AlphaDummy018 A) ≠ (nb081AlphaDummy020 A) := by
  simpa only [nb081AlphaDummy018, nb081AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb081_distinct_020 (A : Class) :
    (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy020 A) := by
  simpa only [nb081AlphaDummy019, nb081AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb081_fresh_021 (x : Var) (y : Var) :
    (nb081AlphaDummy021 x y) ∉
      (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb081AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb081_fresh_022 (x : Var) (y : Var) :
    (nb081AlphaDummy022 x y) ∉
      (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb081AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb081_fresh_023 (x : Var) (y : Var) :
    (nb081AlphaDummy023 x y) ∉
      (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb081AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb081_distinct_024 (x : Var) (y : Var) :
    (nb081AlphaDummy021 x y) ≠ (nb081AlphaDummy022 x y) := by
  simpa only [nb081AlphaDummy021, nb081AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb081_distinct_025 (x : Var) (y : Var) :
    (nb081AlphaDummy021 x y) ≠ (nb081AlphaDummy023 x y) := by
  simpa only [nb081AlphaDummy021, nb081AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb081_distinct_026 (x : Var) (y : Var) :
    (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy023 x y) := by
  simpa only [nb081AlphaDummy022, nb081AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb081_fresh_027 (A : Class) :
    (nb081AlphaDummy030 A) ∉
      (((Class.cv (nb081AlphaDummy019 A))).fv ∪ ((Class.cv (nb081AlphaDummy019 A))).fv) :=
  by
  simpa only [nb081AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb081AlphaDummy019 A))).fv ∪ ((Class.cv (nb081AlphaDummy019 A))).fv)
      0

theorem nb081_fresh_028 (A : Class) :
    (nb081AlphaDummy026 A) ∉
      (((Class.cv (nb081AlphaDummy019 A))).fv ∪ ((Class.cv (nb081AlphaDummy020 A))).fv) :=
  by
  simpa only [nb081AlphaDummy026] using
    freshVar_not_mem
      (((Class.cv (nb081AlphaDummy019 A))).fv ∪ ((Class.cv (nb081AlphaDummy020 A))).fv)
      0

theorem nb081_fresh_029 (A : Class) :
    (nb081AlphaDummy032 A) ∉
      (((Class.cv (nb081AlphaDummy020 A))).fv ∪ ((Class.cv (nb081AlphaDummy020 A))).fv) :=
  by
  simpa only [nb081AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb081AlphaDummy020 A))).fv ∪ ((Class.cv (nb081AlphaDummy020 A))).fv)
      0

theorem nb081_fresh_030 (x : Var) (y : Var) :
    (nb081AlphaDummy031 x y) ∉
      (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy022 x y))).fv) :=
  by
  simpa only [nb081AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy022 x y))).fv)
      0

theorem nb081_fresh_031 (x : Var) (y : Var) :
    (nb081AlphaDummy027 x y) ∉
      (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy023 x y))).fv) :=
  by
  simpa only [nb081AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy023 x y))).fv)
      0

theorem nb081_fresh_032 (x : Var) (y : Var) :
    (nb081AlphaDummy033 x y) ∉
      (((Class.cv (nb081AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy023 x y))).fv) :=
  by
  simpa only [nb081AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb081AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy023 x y))).fv)
      0

theorem nb081_fresh_033 (x : Var) : (nb081AlphaDummy047 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb081AlphaDummy047] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb081_fresh_034 (x : Var) (y : Var) :
    (nb081AlphaDummy006 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb081AlphaDummy006] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb081_fresh_035 (x : Var) (y : Var) :
    (nb081AlphaDummy007 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb081AlphaDummy007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb081_distinct_036 (x : Var) (y : Var) :
    (nb081AlphaDummy006 x y) ≠ (nb081AlphaDummy007 x y) := by
  simpa only [nb081AlphaDummy006, nb081AlphaDummy007] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb081_fresh_037 (y : Var) : (nb081AlphaDummy059 y) ∉ (((Class.cv y)).fv) := by
  simpa only [nb081AlphaDummy059] using freshVar_not_mem (((Class.cv y)).fv) 0

theorem nb081_fresh_038 (A : Class) :
    (nb081AlphaDummy016 A) ∉
      (((Wff.classMem (Class.cv (nb081AlphaDummy012 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb081AlphaDummy012 A)) (synC1c))).fv ∪
        ((Class.cv (nb081AlphaDummy012 A))).fv) :=
  by
  simpa only [nb081AlphaDummy016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb081AlphaDummy012 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb081AlphaDummy012 A)) (synC1c))).fv ∪
        ((Class.cv (nb081AlphaDummy012 A))).fv)
      0

theorem nb081_fresh_039 (x : Var) (y : Var) :
    (nb081AlphaDummy017 x y) ∉
      (((Wff.classMem (Class.cv (nb081AlphaDummy014 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb081AlphaDummy014 x y)) (synC1c))).fv ∪
        ((Class.cv (nb081AlphaDummy014 x y))).fv) :=
  by
  simpa only [nb081AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb081AlphaDummy014 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb081AlphaDummy014 x y)) (synC1c))).fv ∪
        ((Class.cv (nb081AlphaDummy014 x y))).fv)
      0

theorem nb081_fresh_040 (A : Class) :
    (nb081AlphaDummy008 A) ∉
      (((synCcompl (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCphi (Class.cv (nb081AlphaDummy005 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb081AlphaDummy008] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCphi (Class.cv (nb081AlphaDummy005 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb081_fresh_041 (x : Var) (y : Var) :
    (nb081AlphaDummy009 x y) ∉
      (((synCcompl (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCphi (Class.cv (nb081AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb081AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCphi (Class.cv (nb081AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb081_fresh_042 (A : Class) :
    (nb081AlphaDummy028 A) ∉
      (((synCcompl (Class.cv (nb081AlphaDummy019 A)))).fv ∪
        ((synCcompl (Class.cv (nb081AlphaDummy020 A)))).fv) :=
  by
  simpa only [nb081AlphaDummy028] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb081AlphaDummy019 A)))).fv ∪
        ((synCcompl (Class.cv (nb081AlphaDummy020 A)))).fv)
      0

theorem nb081_fresh_043 (x : Var) (y : Var) :
    (nb081AlphaDummy029 x y) ∉
      (((synCcompl (Class.cv (nb081AlphaDummy022 x y)))).fv ∪
        ((synCcompl (Class.cv (nb081AlphaDummy023 x y)))).fv) :=
  by
  simpa only [nb081AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb081AlphaDummy022 x y)))).fv ∪
        ((synCcompl (Class.cv (nb081AlphaDummy023 x y)))).fv)
      0

theorem nb081_fresh_044 (A : Class) :
    (nb081AlphaDummy036 A) ∉
      (((synCcompl (synCphi (Class.cv (nb081AlphaDummy005 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb081AlphaDummy036] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb081AlphaDummy005 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb081_fresh_045 (x : Var) (y : Var) :
    (nb081AlphaDummy037 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb081AlphaDummy007 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb081AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb081AlphaDummy007 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb081_fresh_046 (A : Class) :
    (nb081AlphaDummy052 A) ∉
      (((synCcompl (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb081AlphaDummy001 A))))).fv) :=
  by
  simpa only [nb081AlphaDummy052] using
    freshVar_not_mem
      (((synCcompl (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb081AlphaDummy001 A))))).fv)
      0

theorem nb081_fresh_047 (x : Var) (y : Var) :
    (nb081AlphaDummy053 x y) ∉
      (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv) :=
  by
  simpa only [nb081AlphaDummy053] using
    freshVar_not_mem
      (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv)
      0

theorem nb081_fresh_048 (A : Class) :
    (nb081AlphaDummy040 A) ∉
      (((synCcompl (synCsn (synCsn (Class.cv (nb081AlphaDummy000 A)))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
                (Class.cv (nb081AlphaDummy001 A)))))).fv) :=
  by
  simpa only [nb081AlphaDummy040] using
    freshVar_not_mem
      (((synCcompl (synCsn (synCsn (Class.cv (nb081AlphaDummy000 A)))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
                (Class.cv (nb081AlphaDummy001 A)))))).fv)
      0

theorem nb081_fresh_049 (x : Var) (y : Var) :
    (nb081AlphaDummy041 x y) ∉
      (((synCcompl (synCsn (synCsn (Class.cv x))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb081AlphaDummy041] using
    freshVar_not_mem
      (((synCcompl (synCsn (synCsn (Class.cv x))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb081_fresh_050 (A : Class) :
    (nb081AlphaDummy024 A) ∉
      (((synCnin (Class.cv (nb081AlphaDummy019 A))
            (Class.cv (nb081AlphaDummy020 A)))).fv ∪
        ((synCnin (Class.cv (nb081AlphaDummy019 A))
            (Class.cv (nb081AlphaDummy020 A)))).fv) :=
  by
  simpa only [nb081AlphaDummy024] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb081AlphaDummy019 A))
            (Class.cv (nb081AlphaDummy020 A)))).fv ∪
        ((synCnin (Class.cv (nb081AlphaDummy019 A))
            (Class.cv (nb081AlphaDummy020 A)))).fv)
      0

theorem nb081_fresh_051 (x : Var) (y : Var) :
    (nb081AlphaDummy025 x y) ∉
      (((synCnin (Class.cv (nb081AlphaDummy022 x y))
            (Class.cv (nb081AlphaDummy023 x y)))).fv ∪
        ((synCnin (Class.cv (nb081AlphaDummy022 x y))
            (Class.cv (nb081AlphaDummy023 x y)))).fv) :=
  by
  simpa only [nb081AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb081AlphaDummy022 x y))
            (Class.cv (nb081AlphaDummy023 x y)))).fv ∪
        ((synCnin (Class.cv (nb081AlphaDummy022 x y))
            (Class.cv (nb081AlphaDummy023 x y)))).fv)
      0

theorem nb081_fresh_052 (A : Class) :
    (nb081AlphaDummy038 A) ∉
      (((synCphi (Class.cv (nb081AlphaDummy005 A)))).fv ∪
        ((synCphi (Class.cv (nb081AlphaDummy005 A)))).fv) :=
  by
  simpa only [nb081AlphaDummy038] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb081AlphaDummy005 A)))).fv ∪
        ((synCphi (Class.cv (nb081AlphaDummy005 A)))).fv)
      0

theorem nb081_fresh_053 (x : Var) (y : Var) :
    (nb081AlphaDummy039 x y) ∉
      (((synCphi (Class.cv (nb081AlphaDummy007 x y)))).fv ∪
        ((synCphi (Class.cv (nb081AlphaDummy007 x y)))).fv) :=
  by
  simpa only [nb081AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb081AlphaDummy007 x y)))).fv ∪
        ((synCphi (Class.cv (nb081AlphaDummy007 x y)))).fv)
      0

theorem nb081_fresh_054 (A : Class) :
    (nb081AlphaDummy050 A) ∉
      (((synCpr (Class.cv (nb081AlphaDummy000 A))
          (Class.cv (nb081AlphaDummy001 A)))).fv) :=
  by
  simpa only [nb081AlphaDummy050] using
    freshVar_not_mem
      (((synCpr (Class.cv (nb081AlphaDummy000 A)) (Class.cv (nb081AlphaDummy001 A)))).fv)
      0

theorem nb081_fresh_055 (x : Var) (y : Var) :
    (nb081AlphaDummy051 x y) ∉ (((synCpr (Class.cv x) (Class.cv y))).fv) := by
  simpa only [nb081AlphaDummy051] using
    freshVar_not_mem (((synCpr (Class.cv x) (Class.cv y))).fv) 0

theorem nb081_fresh_056 (A : Class) :
    (nb081AlphaDummy044 A) ∉ (((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb081AlphaDummy044] using
    freshVar_not_mem (((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv) 0

theorem nb081_fresh_057 (A : Class) :
    (nb081AlphaDummy054 A) ∉
      (((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv ∪
        ((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb081AlphaDummy054] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv ∪
        ((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv)
      0

theorem nb081_fresh_058 (A : Class) :
    (nb081AlphaDummy056 A) ∉
      (((synCsn (Class.cv (nb081AlphaDummy001 A)))).fv ∪
        ((synCsn (Class.cv (nb081AlphaDummy001 A)))).fv) :=
  by
  simpa only [nb081AlphaDummy056] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb081AlphaDummy001 A)))).fv ∪
        ((synCsn (Class.cv (nb081AlphaDummy001 A)))).fv)
      0

theorem nb081_fresh_059 (x : Var) :
    (nb081AlphaDummy045 x) ∉ (((synCsn (Class.cv x))).fv) := by
  simpa only [nb081AlphaDummy045] using
    freshVar_not_mem (((synCsn (Class.cv x))).fv) 0

theorem nb081_fresh_060 (x : Var) :
    (nb081AlphaDummy055 x) ∉
      (((synCsn (Class.cv x))).fv ∪ ((synCsn (Class.cv x))).fv) :=
  by
  simpa only [nb081AlphaDummy055] using
    freshVar_not_mem (((synCsn (Class.cv x))).fv ∪ ((synCsn (Class.cv x))).fv) 0

theorem nb081_fresh_061 (y : Var) :
    (nb081AlphaDummy057 y) ∉
      (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) :=
  by
  simpa only [nb081AlphaDummy057] using
    freshVar_not_mem (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) 0

theorem nb081_fresh_062 (A : Class) :
    (nb081AlphaDummy048 A) ∉
      (((synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))))).fv) :=
  by
  simpa only [nb081AlphaDummy048] using
    freshVar_not_mem
      (((synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))))).fv)
      0

theorem nb081_fresh_063 (x : Var) (y : Var) :
    (nb081AlphaDummy049 x y) ∉
      (((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv ∪
        ((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv) :=
  by
  simpa only [nb081AlphaDummy049] using
    freshVar_not_mem
      (((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv ∪
        ((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv)
      0

theorem nb081_fresh_064 (A : Class) :
    (nb081AlphaDummy042 A) ∉
      (((synCsn (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv) :=
  by
  simpa only [nb081AlphaDummy042] using
    freshVar_not_mem
      (((synCsn (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv)
      0

theorem nb081_fresh_065 (x : Var) :
    (nb081AlphaDummy043 x) ∉
      (((synCsn (synCsn (Class.cv x)))).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) :=
  by
  simpa only [nb081AlphaDummy043] using
    freshVar_not_mem
      (((synCsn (synCsn (Class.cv x)))).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) 0

theorem nb081_fresh_066 (A : Class) : (nb081AlphaDummy000 A) ∉ ((A).fv) := by
  simpa only [nb081AlphaDummy000] using freshVar_not_mem ((A).fv) 0

theorem nb081_fresh_067 (A : Class) : (nb081AlphaDummy001 A) ∉ ((A).fv) := by
  simpa only [nb081AlphaDummy001] using freshVar_not_mem ((A).fv) 1

theorem nb081_distinct_068 (A : Class) :
    (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy001 A) := by
  simpa only [nb081AlphaDummy000, nb081AlphaDummy001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb081_fresh_069 (A : Class) :
    (nb081AlphaDummy002 A) ∉
      (({(nb081AlphaDummy000 A)} : Finset Var) ∪ ({(nb081AlphaDummy001 A)} : Finset Var) ∪
        ((Wff.classMem (synCopk (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))) A)).fv) :=
  by
  simpa only [nb081AlphaDummy002] using
    freshVar_not_mem
      (({(nb081AlphaDummy000 A)} : Finset Var) ∪ ({(nb081AlphaDummy001 A)} : Finset Var) ∪
        ((Wff.classMem (synCopk (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))) A)).fv)
      0

theorem nb081_fresh_070 (x : Var) (y : Var) (A : Class) :
    (nb081AlphaDummy003 x y A) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classMem (synCopk (Class.cv x) (Class.cv y)) A)).fv) :=
  by
  simpa only [nb081AlphaDummy003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classMem (synCopk (Class.cv x) (Class.cv y)) A)).fv)
      0

theorem nb081_support_mem_0000 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (({(nb081AlphaDummy000 A)} : Finset Var) ∪ ({(nb081AlphaDummy001 A)} : Finset Var) ∪
        ((Wff.classMem (synCopk (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))) A)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0001 (x : Var) (y : Var) (A : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classMem (synCopk (Class.cv x) (Class.cv y)) A)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0002 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (({(nb081AlphaDummy000 A)} : Finset Var) ∪ ({(nb081AlphaDummy001 A)} : Finset Var) ∪
        ((Wff.classMem (synCopk (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))) A)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0003 (x : Var) (y : Var) (A : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classMem (synCopk (Class.cv x) (Class.cv y)) A)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0004 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((Class.cv (nb081AlphaDummy000 A))).fv ∪ ((Class.cv (nb081AlphaDummy001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0005 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((synCcompl (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCphi (Class.cv (nb081AlphaDummy005 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy004 A) from (by
          unfold nb081AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy005 A) from (by
            unfold nb081AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0006 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCphi (Class.cv (nb081AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb081AlphaDummy006 x y) from (by
          unfold nb081AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0006 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb081AlphaDummy007 x y) from (by
            unfold nb081AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0006 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0008 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCphi (Class.cv (nb081AlphaDummy005 A))))))).fv ∪
        ((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCphi (Class.cv (nb081AlphaDummy005 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy004 A) from (by
          unfold nb081AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy005 A) from (by
            unfold nb081AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCphi (Class.cv (nb081AlphaDummy007 x y))))))).fv ∪
        ((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCphi (Class.cv (nb081AlphaDummy007 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb081AlphaDummy006 x y) from (by
          unfold nb081AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0006 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb081AlphaDummy007 x y) from (by
            unfold nb081AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0006 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0010 (A : Class) :
    (nb081AlphaDummy005 A) ∈ (((Class.cv (nb081AlphaDummy005 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0011 (x : Var) (y : Var) :
    (nb081AlphaDummy007 x y) ∈ (((Class.cv (nb081AlphaDummy007 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0012 (A : Class) :
    (nb081AlphaDummy012 A) ∈
      (((Wff.classMem (Class.cv (nb081AlphaDummy012 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb081AlphaDummy012 A)) (synC1c))).fv ∪
        ((Class.cv (nb081AlphaDummy012 A))).fv) :=
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

theorem nb081_support_mem_0013 (x : Var) (y : Var) :
    (nb081AlphaDummy014 x y) ∈
      (((Wff.classMem (Class.cv (nb081AlphaDummy014 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb081AlphaDummy014 x y)) (synC1c))).fv ∪
        ((Class.cv (nb081AlphaDummy014 x y))).fv) :=
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

theorem nb081_support_mem_0014 (A : Class) :
    (nb081AlphaDummy012 A) ∈
      (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0015 (x : Var) (y : Var) :
    (nb081AlphaDummy014 x y) ∈
      (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0016 (A : Class) :
    (nb081AlphaDummy019 A) ∈
      (((synCnin (Class.cv (nb081AlphaDummy019 A))
            (Class.cv (nb081AlphaDummy020 A)))).fv ∪
        ((synCnin (Class.cv (nb081AlphaDummy019 A))
            (Class.cv (nb081AlphaDummy020 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0017 (x : Var) (y : Var) :
    (nb081AlphaDummy022 x y) ∈
      (((synCnin (Class.cv (nb081AlphaDummy022 x y))
            (Class.cv (nb081AlphaDummy023 x y)))).fv ∪
        ((synCnin (Class.cv (nb081AlphaDummy022 x y))
            (Class.cv (nb081AlphaDummy023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0018 (A : Class) :
    (nb081AlphaDummy019 A) ∈
      (((Class.cv (nb081AlphaDummy019 A))).fv ∪ ((Class.cv (nb081AlphaDummy020 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C081C001Part002`. -/


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

theorem nb081_support_mem_0019 (x : Var) (y : Var) :
    (nb081AlphaDummy022 x y) ∈
      (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0020 (A : Class) :
    (nb081AlphaDummy020 A) ∈
      (((synCnin (Class.cv (nb081AlphaDummy019 A))
            (Class.cv (nb081AlphaDummy020 A)))).fv ∪
        ((synCnin (Class.cv (nb081AlphaDummy019 A))
            (Class.cv (nb081AlphaDummy020 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0021 (x : Var) (y : Var) :
    (nb081AlphaDummy023 x y) ∈
      (((synCnin (Class.cv (nb081AlphaDummy022 x y))
            (Class.cv (nb081AlphaDummy023 x y)))).fv ∪
        ((synCnin (Class.cv (nb081AlphaDummy022 x y))
            (Class.cv (nb081AlphaDummy023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0022 (A : Class) :
    (nb081AlphaDummy020 A) ∈
      (((Class.cv (nb081AlphaDummy019 A))).fv ∪ ((Class.cv (nb081AlphaDummy020 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0023 (x : Var) (y : Var) :
    (nb081AlphaDummy023 x y) ∈
      (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0024 (A : Class) :
    (nb081AlphaDummy019 A) ∈
      (((synCcompl (Class.cv (nb081AlphaDummy019 A)))).fv ∪
        ((synCcompl (Class.cv (nb081AlphaDummy020 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0025 (x : Var) (y : Var) :
    (nb081AlphaDummy022 x y) ∈
      (((synCcompl (Class.cv (nb081AlphaDummy022 x y)))).fv ∪
        ((synCcompl (Class.cv (nb081AlphaDummy023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0026 (A : Class) :
    (nb081AlphaDummy019 A) ∈
      (((Class.cv (nb081AlphaDummy019 A))).fv ∪ ((Class.cv (nb081AlphaDummy019 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0027 (x : Var) (y : Var) :
    (nb081AlphaDummy022 x y) ∈
      (((Class.cv (nb081AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy022 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0028 (A : Class) :
    (nb081AlphaDummy020 A) ∈
      (((synCcompl (Class.cv (nb081AlphaDummy019 A)))).fv ∪
        ((synCcompl (Class.cv (nb081AlphaDummy020 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0029 (x : Var) (y : Var) :
    (nb081AlphaDummy023 x y) ∈
      (((synCcompl (Class.cv (nb081AlphaDummy022 x y)))).fv ∪
        ((synCcompl (Class.cv (nb081AlphaDummy023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0030 (A : Class) :
    (nb081AlphaDummy020 A) ∈
      (((Class.cv (nb081AlphaDummy020 A))).fv ∪ ((Class.cv (nb081AlphaDummy020 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0031 (x : Var) (y : Var) :
    (nb081AlphaDummy023 x y) ∈
      (((Class.cv (nb081AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb081AlphaDummy023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0032 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (((Class.cv (nb081AlphaDummy000 A))).fv ∪ ((Class.cv (nb081AlphaDummy001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0033 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (((synCcompl (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCphi (Class.cv (nb081AlphaDummy005 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy004 A) from (by
          unfold nb081AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy005 A) from (by
            unfold nb081AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0034 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0035 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCphi (Class.cv (nb081AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb081AlphaDummy006 x y) from (by
          unfold nb081AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb081AlphaDummy007 x y) from (by
            unfold nb081AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0036 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy004 A) from (by
          unfold nb081AlphaDummy004;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy005 A) from (by
            unfold nb081AlphaDummy005;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0037 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb081AlphaDummy006 x y) from (by
          unfold nb081AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb081AlphaDummy007 x y) from (by
            unfold nb081AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0038 (A : Class) :
    (nb081AlphaDummy005 A) ∈
      (((synCcompl (synCphi (Class.cv (nb081AlphaDummy005 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0039 (x : Var) (y : Var) :
    (nb081AlphaDummy007 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb081AlphaDummy007 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0040 (A : Class) :
    (nb081AlphaDummy005 A) ∈
      (((synCphi (Class.cv (nb081AlphaDummy005 A)))).fv ∪
        ((synCphi (Class.cv (nb081AlphaDummy005 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0041 (x : Var) (y : Var) :
    (nb081AlphaDummy007 x y) ∈
      (((synCphi (Class.cv (nb081AlphaDummy007 x y)))).fv ∪
        ((synCphi (Class.cv (nb081AlphaDummy007 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0042 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((synCcompl (synCsn (synCsn (Class.cv (nb081AlphaDummy000 A)))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
                (Class.cv (nb081AlphaDummy001 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0043 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (synCsn (synCsn (Class.cv x))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0044 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((synCsn (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0045 (x : Var) :
    x ∈ (((synCsn (synCsn (Class.cv x)))).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0046 (A : Class) :
    (nb081AlphaDummy000 A) ∈ (((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0047 (x : Var) : x ∈ (((synCsn (Class.cv x))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0048 (A : Class) :
    (nb081AlphaDummy000 A) ∈ (((Class.cv (nb081AlphaDummy000 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0049 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0050 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0051 (x : Var) (y : Var) :
    x ∈
      (((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv ∪
        ((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0052 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((synCpr (Class.cv (nb081AlphaDummy000 A))
          (Class.cv (nb081AlphaDummy001 A)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0053 (x : Var) (y : Var) :
    x ∈ (((synCpr (Class.cv x) (Class.cv y))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0054 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((synCcompl (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb081AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0055 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0056 (A : Class) :
    (nb081AlphaDummy000 A) ∈
      (((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv ∪
        ((synCsn (Class.cv (nb081AlphaDummy000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0057 (x : Var) :
    x ∈ (((synCsn (Class.cv x))).fv ∪ ((synCsn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0058 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (((synCcompl (synCsn (synCsn (Class.cv (nb081AlphaDummy000 A)))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
                (Class.cv (nb081AlphaDummy001 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0059 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (synCsn (synCsn (Class.cv x))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv x) (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0060 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (((synCsn (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0061 (x : Var) (y : Var) :
    y ∈
      (((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv ∪
        ((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0062 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (((synCpr (Class.cv (nb081AlphaDummy000 A))
          (Class.cv (nb081AlphaDummy001 A)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0063 (x : Var) (y : Var) :
    y ∈ (((synCpr (Class.cv x) (Class.cv y))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0064 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (((synCcompl (synCsn (Class.cv (nb081AlphaDummy000 A))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb081AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0065 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0066 (A : Class) :
    (nb081AlphaDummy001 A) ∈
      (((synCsn (Class.cv (nb081AlphaDummy001 A)))).fv ∪
        ((synCsn (Class.cv (nb081AlphaDummy001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0067 (y : Var) :
    y ∈ (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0068 (A : Class) :
    (nb081AlphaDummy001 A) ∈ (((Class.cv (nb081AlphaDummy001 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0069 (y : Var) : y ∈ (((Class.cv y)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
