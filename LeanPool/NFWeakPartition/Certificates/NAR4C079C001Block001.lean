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

/-! Certificates from `NAR4C079C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_000`. -/
@[expose]
noncomputable def nb079AlphaDummy000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_001`. -/
@[expose]
noncomputable def nb079AlphaDummy001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_002`. -/
@[expose]
noncomputable def nb079AlphaDummy002 (A : Class) : Var :=
  (freshVar ((A).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_003`. -/
@[expose]
noncomputable def nb079AlphaDummy003 (A : Class) : Var :=
  (freshVar (((synCcompl (synCsn (synCsn (Class.cv (nb079AlphaDummy000 A)))))).fv ∪
      ((synCcompl (synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_004`. -/
@[expose]
noncomputable def nb079AlphaDummy004 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCsn (synCsn (Class.cv x))))).fv ∪
      ((synCcompl (synCsn (synCpr (Class.cv x) (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_005`. -/
@[expose]
noncomputable def nb079AlphaDummy005 (A : Class) : Var :=
  (freshVar (((synCsn (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
      ((synCsn (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_006`. -/
@[expose]
noncomputable def nb079AlphaDummy006 (x : Var) : Var :=
  (freshVar (((synCsn (synCsn (Class.cv x)))).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_007`. -/
@[expose]
noncomputable def nb079AlphaDummy007 (A : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_008`. -/
@[expose]
noncomputable def nb079AlphaDummy008 (x : Var) : Var :=
  (freshVar (((synCsn (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_009`. -/
@[expose]
noncomputable def nb079AlphaDummy009 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy000 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_010`. -/
@[expose]
noncomputable def nb079AlphaDummy010 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_011`. -/
@[expose]
noncomputable def nb079AlphaDummy011 (A : Class) : Var :=
  (freshVar (((synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
            (Class.cv (nb079AlphaDummy001 A))))).fv ∪ ((synCsn
          (synCpr (Class.cv (nb079AlphaDummy000 A))
            (Class.cv (nb079AlphaDummy001 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_012`. -/
@[expose]
noncomputable def nb079AlphaDummy012 (x : Var) (y : Var) : Var :=
  (freshVar (((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv ∪
      ((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_013`. -/
@[expose]
noncomputable def nb079AlphaDummy013 (A : Class) : Var :=
  (freshVar (((synCpr (Class.cv (nb079AlphaDummy000 A))
        (Class.cv (nb079AlphaDummy001 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_014`. -/
@[expose]
noncomputable def nb079AlphaDummy014 (x : Var) (y : Var) : Var :=
  (freshVar (((synCpr (Class.cv x) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_015`. -/
@[expose]
noncomputable def nb079AlphaDummy015 (A : Class) : Var :=
  (freshVar (((synCcompl (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
      ((synCcompl (synCsn (Class.cv (nb079AlphaDummy001 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_016`. -/
@[expose]
noncomputable def nb079AlphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar
    (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_017`. -/
@[expose]
noncomputable def nb079AlphaDummy017 (A : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv ∪
      ((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_018`. -/
@[expose]
noncomputable def nb079AlphaDummy018 (x : Var) : Var :=
  (freshVar (((synCsn (Class.cv x))).fv ∪ ((synCsn (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_019`. -/
@[expose]
noncomputable def nb079AlphaDummy019 (A : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb079AlphaDummy001 A)))).fv ∪
      ((synCsn (Class.cv (nb079AlphaDummy001 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_020`. -/
@[expose]
noncomputable def nb079AlphaDummy020 (y : Var) : Var :=
  (freshVar (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_021`. -/
@[expose]
noncomputable def nb079AlphaDummy021 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_022`. -/
@[expose]
noncomputable def nb079AlphaDummy022 (y : Var) : Var :=
  (freshVar (((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_023`. -/
@[expose]
noncomputable def nb079AlphaDummy023 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy000 A))).fv ∪
      ((Class.cv (nb079AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_024`. -/
@[expose]
noncomputable def nb079AlphaDummy024 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy000 A))).fv ∪
      ((Class.cv (nb079AlphaDummy001 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_025`. -/
@[expose]
noncomputable def nb079AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_026`. -/
@[expose]
noncomputable def nb079AlphaDummy026 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_027`. -/
@[expose]
noncomputable def nb079AlphaDummy027 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCphi (Class.cv (nb079AlphaDummy024 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_028`. -/
@[expose]
noncomputable def nb079AlphaDummy028 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCphi (Class.cv (nb079AlphaDummy026 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_029`. -/
@[expose]
noncomputable def nb079AlphaDummy029 (A : Class) : Var :=
  (freshVar (((Class.cab (nb079AlphaDummy023 A)
          (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
            (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
              (synCphi (Class.cv (nb079AlphaDummy024 A))))))).fv ∪
      ((Class.cab (nb079AlphaDummy023 A)
          (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
            (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
              (synCphi (Class.cv (nb079AlphaDummy024 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_030`. -/
@[expose]
noncomputable def nb079AlphaDummy030 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb079AlphaDummy025 x y)
          (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
              (synCphi (Class.cv (nb079AlphaDummy026 x y))))))).fv ∪
      ((Class.cab (nb079AlphaDummy025 x y) (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
              (synCphi (Class.cv (nb079AlphaDummy026 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_031`. -/
@[expose]
noncomputable def nb079AlphaDummy031 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy024 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_032`. -/
@[expose]
noncomputable def nb079AlphaDummy032 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy024 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_033`. -/
@[expose]
noncomputable def nb079AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy026 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_034`. -/
@[expose]
noncomputable def nb079AlphaDummy034 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy026 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_035`. -/
@[expose]
noncomputable def nb079AlphaDummy035 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb079AlphaDummy031 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb079AlphaDummy031 A)) (synC1c))).fv ∪
      ((Class.cv (nb079AlphaDummy031 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_036`. -/
@[expose]
noncomputable def nb079AlphaDummy036 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb079AlphaDummy033 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb079AlphaDummy033 x y)) (synC1c))).fv ∪
      ((Class.cv (nb079AlphaDummy033 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_037`. -/
@[expose]
noncomputable def nb079AlphaDummy037 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_038`. -/
@[expose]
noncomputable def nb079AlphaDummy038 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_039`. -/
@[expose]
noncomputable def nb079AlphaDummy039 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_040`. -/
@[expose]
noncomputable def nb079AlphaDummy040 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_041`. -/
@[expose]
noncomputable def nb079AlphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_042`. -/
@[expose]
noncomputable def nb079AlphaDummy042 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_043`. -/
@[expose]
noncomputable def nb079AlphaDummy043 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb079AlphaDummy038 A))
          (Class.cv (nb079AlphaDummy039 A)))).fv ∪
      ((synCnin (Class.cv (nb079AlphaDummy038 A)) (Class.cv (nb079AlphaDummy039 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_044`. -/
@[expose]
noncomputable def nb079AlphaDummy044 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb079AlphaDummy041 x y))
          (Class.cv (nb079AlphaDummy042 x y)))).fv ∪
      ((synCnin (Class.cv (nb079AlphaDummy041 x y))
          (Class.cv (nb079AlphaDummy042 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_045`. -/
@[expose]
noncomputable def nb079AlphaDummy045 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy038 A))).fv ∪
      ((Class.cv (nb079AlphaDummy039 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_046`. -/
@[expose]
noncomputable def nb079AlphaDummy046 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
      ((Class.cv (nb079AlphaDummy042 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_047`. -/
@[expose]
noncomputable def nb079AlphaDummy047 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb079AlphaDummy038 A)))).fv ∪
      ((synCcompl (Class.cv (nb079AlphaDummy039 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_048`. -/
@[expose]
noncomputable def nb079AlphaDummy048 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb079AlphaDummy041 x y)))).fv ∪
      ((synCcompl (Class.cv (nb079AlphaDummy042 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_049`. -/
@[expose]
noncomputable def nb079AlphaDummy049 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy038 A))).fv ∪
      ((Class.cv (nb079AlphaDummy038 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_050`. -/
@[expose]
noncomputable def nb079AlphaDummy050 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
      ((Class.cv (nb079AlphaDummy041 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_051`. -/
@[expose]
noncomputable def nb079AlphaDummy051 (A : Class) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy039 A))).fv ∪
      ((Class.cv (nb079AlphaDummy039 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_052`. -/
@[expose]
noncomputable def nb079AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb079AlphaDummy042 x y))).fv ∪
      ((Class.cv (nb079AlphaDummy042 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_053`. -/
@[expose]
noncomputable def nb079AlphaDummy053 (A : Class) : Var :=
  (freshVar (((Class.cab (nb079AlphaDummy023 A)
          (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
              (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb079AlphaDummy023 A)
          (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
              (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_054`. -/
@[expose]
noncomputable def nb079AlphaDummy054 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb079AlphaDummy025 x y)
          (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
              (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb079AlphaDummy025 x y)
          (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
              (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_055`. -/
@[expose]
noncomputable def nb079AlphaDummy055 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb079AlphaDummy024 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_056`. -/
@[expose]
noncomputable def nb079AlphaDummy056 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb079AlphaDummy026 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_057`. -/
@[expose]
noncomputable def nb079AlphaDummy057 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb079AlphaDummy024 A)))).fv ∪
      ((synCphi (Class.cv (nb079AlphaDummy024 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb079_alpha_dummy_058`. -/
@[expose]
noncomputable def nb079AlphaDummy058 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb079AlphaDummy026 x y)))).fv ∪
      ((synCphi (Class.cv (nb079AlphaDummy026 x y)))).fv) 0)

theorem nb079_fresh_000 (A : Class) :
    (nb079AlphaDummy029 A) ∉
      (((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCphi (Class.cv (nb079AlphaDummy024 A))))))).fv ∪
        ((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCphi (Class.cv (nb079AlphaDummy024 A))))))).fv) :=
  by
  simpa only [nb079AlphaDummy029] using
    freshVar_not_mem
      (((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCphi (Class.cv (nb079AlphaDummy024 A))))))).fv ∪
        ((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCphi (Class.cv (nb079AlphaDummy024 A))))))).fv)
      0

theorem nb079_fresh_001 (A : Class) :
    (nb079AlphaDummy053 A) ∉
      (((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb079AlphaDummy053] using
    freshVar_not_mem
      (((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb079_fresh_002 (x : Var) (y : Var) :
    (nb079AlphaDummy030 x y) ∉
      (((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCphi (Class.cv (nb079AlphaDummy026 x y))))))).fv ∪
        ((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCphi (Class.cv (nb079AlphaDummy026 x y))))))).fv) :=
  by
  simpa only [nb079AlphaDummy030] using
    freshVar_not_mem
      (((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCphi (Class.cv (nb079AlphaDummy026 x y))))))).fv ∪
        ((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCphi (Class.cv (nb079AlphaDummy026 x y))))))).fv)
      0

theorem nb079_fresh_003 (x : Var) (y : Var) :
    (nb079AlphaDummy054 x y) ∉
      (((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb079AlphaDummy054] using
    freshVar_not_mem
      (((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb079_fresh_004 (A : Class) :
    (nb079AlphaDummy009 A) ∉ (((Class.cv (nb079AlphaDummy000 A))).fv) := by
  simpa only [nb079AlphaDummy009] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy000 A))).fv) 0

theorem nb079_fresh_005 (A : Class) :
    (nb079AlphaDummy023 A) ∉
      (((Class.cv (nb079AlphaDummy000 A))).fv ∪ ((Class.cv (nb079AlphaDummy001 A))).fv) :=
  by
  simpa only [nb079AlphaDummy023] using
    freshVar_not_mem
      (((Class.cv (nb079AlphaDummy000 A))).fv ∪ ((Class.cv (nb079AlphaDummy001 A))).fv)
      0

theorem nb079_fresh_006 (A : Class) :
    (nb079AlphaDummy024 A) ∉
      (((Class.cv (nb079AlphaDummy000 A))).fv ∪ ((Class.cv (nb079AlphaDummy001 A))).fv) :=
  by
  simpa only [nb079AlphaDummy024] using
    freshVar_not_mem
      (((Class.cv (nb079AlphaDummy000 A))).fv ∪ ((Class.cv (nb079AlphaDummy001 A))).fv)
      1

theorem nb079_distinct_007 (A : Class) :
    (nb079AlphaDummy023 A) ≠ (nb079AlphaDummy024 A) := by
  simpa only [nb079AlphaDummy023, nb079AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy000 A))).fv ∪
        ((Class.cv (nb079AlphaDummy001 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb079_fresh_008 (A : Class) :
    (nb079AlphaDummy021 A) ∉ (((Class.cv (nb079AlphaDummy001 A))).fv) := by
  simpa only [nb079AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy001 A))).fv) 0

theorem nb079_fresh_009 (A : Class) :
    (nb079AlphaDummy031 A) ∉ (((Class.cv (nb079AlphaDummy024 A))).fv) := by
  simpa only [nb079AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy024 A))).fv) 0

theorem nb079_fresh_010 (A : Class) :
    (nb079AlphaDummy032 A) ∉ (((Class.cv (nb079AlphaDummy024 A))).fv) := by
  simpa only [nb079AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy024 A))).fv) 1

theorem nb079_distinct_011 (A : Class) :
    (nb079AlphaDummy031 A) ≠ (nb079AlphaDummy032 A) := by
  simpa only [nb079AlphaDummy031, nb079AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy024 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb079_fresh_012 (x : Var) (y : Var) :
    (nb079AlphaDummy033 x y) ∉ (((Class.cv (nb079AlphaDummy026 x y))).fv) := by
  simpa only [nb079AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy026 x y))).fv) 0

theorem nb079_fresh_013 (x : Var) (y : Var) :
    (nb079AlphaDummy034 x y) ∉ (((Class.cv (nb079AlphaDummy026 x y))).fv) := by
  simpa only [nb079AlphaDummy034] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy026 x y))).fv) 1

theorem nb079_distinct_014 (x : Var) (y : Var) :
    (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy034 x y) := by
  simpa only [nb079AlphaDummy033, nb079AlphaDummy034] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy026 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb079_fresh_015 (A : Class) :
    (nb079AlphaDummy037 A) ∉
      (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb079AlphaDummy037] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) 0

theorem nb079_fresh_016 (A : Class) :
    (nb079AlphaDummy038 A) ∉
      (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb079AlphaDummy038] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) 1

theorem nb079_fresh_017 (A : Class) :
    (nb079AlphaDummy039 A) ∉
      (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb079AlphaDummy039] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) 2

theorem nb079_distinct_018 (A : Class) :
    (nb079AlphaDummy037 A) ≠ (nb079AlphaDummy038 A) := by
  simpa only [nb079AlphaDummy037, nb079AlphaDummy038] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb079_distinct_019 (A : Class) :
    (nb079AlphaDummy037 A) ≠ (nb079AlphaDummy039 A) := by
  simpa only [nb079AlphaDummy037, nb079AlphaDummy039] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb079_distinct_020 (A : Class) :
    (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy039 A) := by
  simpa only [nb079AlphaDummy038, nb079AlphaDummy039] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb079_fresh_021 (x : Var) (y : Var) :
    (nb079AlphaDummy040 x y) ∉
      (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb079AlphaDummy040] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb079_fresh_022 (x : Var) (y : Var) :
    (nb079AlphaDummy041 x y) ∉
      (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb079AlphaDummy041] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb079_fresh_023 (x : Var) (y : Var) :
    (nb079AlphaDummy042 x y) ∉
      (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb079AlphaDummy042] using
    freshVar_not_mem (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb079_distinct_024 (x : Var) (y : Var) :
    (nb079AlphaDummy040 x y) ≠ (nb079AlphaDummy041 x y) := by
  simpa only [nb079AlphaDummy040, nb079AlphaDummy041] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb079_distinct_025 (x : Var) (y : Var) :
    (nb079AlphaDummy040 x y) ≠ (nb079AlphaDummy042 x y) := by
  simpa only [nb079AlphaDummy040, nb079AlphaDummy042] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb079_distinct_026 (x : Var) (y : Var) :
    (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy042 x y) := by
  simpa only [nb079AlphaDummy041, nb079AlphaDummy042] using
    (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb079_fresh_027 (A : Class) :
    (nb079AlphaDummy049 A) ∉
      (((Class.cv (nb079AlphaDummy038 A))).fv ∪ ((Class.cv (nb079AlphaDummy038 A))).fv) :=
  by
  simpa only [nb079AlphaDummy049] using
    freshVar_not_mem
      (((Class.cv (nb079AlphaDummy038 A))).fv ∪ ((Class.cv (nb079AlphaDummy038 A))).fv)
      0

theorem nb079_fresh_028 (A : Class) :
    (nb079AlphaDummy045 A) ∉
      (((Class.cv (nb079AlphaDummy038 A))).fv ∪ ((Class.cv (nb079AlphaDummy039 A))).fv) :=
  by
  simpa only [nb079AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb079AlphaDummy038 A))).fv ∪ ((Class.cv (nb079AlphaDummy039 A))).fv)
      0

theorem nb079_fresh_029 (A : Class) :
    (nb079AlphaDummy051 A) ∉
      (((Class.cv (nb079AlphaDummy039 A))).fv ∪ ((Class.cv (nb079AlphaDummy039 A))).fv) :=
  by
  simpa only [nb079AlphaDummy051] using
    freshVar_not_mem
      (((Class.cv (nb079AlphaDummy039 A))).fv ∪ ((Class.cv (nb079AlphaDummy039 A))).fv)
      0

theorem nb079_fresh_030 (x : Var) (y : Var) :
    (nb079AlphaDummy050 x y) ∉
      (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy041 x y))).fv) :=
  by
  simpa only [nb079AlphaDummy050] using
    freshVar_not_mem
      (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy041 x y))).fv)
      0

theorem nb079_fresh_031 (x : Var) (y : Var) :
    (nb079AlphaDummy046 x y) ∉
      (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy042 x y))).fv) :=
  by
  simpa only [nb079AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy042 x y))).fv)
      0

theorem nb079_fresh_032 (x : Var) (y : Var) :
    (nb079AlphaDummy052 x y) ∉
      (((Class.cv (nb079AlphaDummy042 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy042 x y))).fv) :=
  by
  simpa only [nb079AlphaDummy052] using
    freshVar_not_mem
      (((Class.cv (nb079AlphaDummy042 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy042 x y))).fv)
      0

theorem nb079_fresh_033 (x : Var) : (nb079AlphaDummy010 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb079AlphaDummy010] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb079_fresh_034 (x : Var) (y : Var) :
    (nb079AlphaDummy025 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb079AlphaDummy025] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb079_fresh_035 (x : Var) (y : Var) :
    (nb079AlphaDummy026 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb079AlphaDummy026] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb079_distinct_036 (x : Var) (y : Var) :
    (nb079AlphaDummy025 x y) ≠ (nb079AlphaDummy026 x y) := by
  simpa only [nb079AlphaDummy025, nb079AlphaDummy026] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb079_fresh_037 (y : Var) : (nb079AlphaDummy022 y) ∉ (((Class.cv y)).fv) := by
  simpa only [nb079AlphaDummy022] using freshVar_not_mem (((Class.cv y)).fv) 0

theorem nb079_fresh_038 (A : Class) :
    (nb079AlphaDummy035 A) ∉
      (((Wff.classMem (Class.cv (nb079AlphaDummy031 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb079AlphaDummy031 A)) (synC1c))).fv ∪
        ((Class.cv (nb079AlphaDummy031 A))).fv) :=
  by
  simpa only [nb079AlphaDummy035] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb079AlphaDummy031 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb079AlphaDummy031 A)) (synC1c))).fv ∪
        ((Class.cv (nb079AlphaDummy031 A))).fv)
      0

theorem nb079_fresh_039 (x : Var) (y : Var) :
    (nb079AlphaDummy036 x y) ∉
      (((Wff.classMem (Class.cv (nb079AlphaDummy033 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb079AlphaDummy033 x y)) (synC1c))).fv ∪
        ((Class.cv (nb079AlphaDummy033 x y))).fv) :=
  by
  simpa only [nb079AlphaDummy036] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb079AlphaDummy033 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb079AlphaDummy033 x y)) (synC1c))).fv ∪
        ((Class.cv (nb079AlphaDummy033 x y))).fv)
      0

theorem nb079_fresh_040 (A : Class) :
    (nb079AlphaDummy027 A) ∉
      (((synCcompl (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCphi (Class.cv (nb079AlphaDummy024 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb079AlphaDummy027] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCphi (Class.cv (nb079AlphaDummy024 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb079_fresh_041 (x : Var) (y : Var) :
    (nb079AlphaDummy028 x y) ∉
      (((synCcompl (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCphi (Class.cv (nb079AlphaDummy026 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb079AlphaDummy028] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCphi (Class.cv (nb079AlphaDummy026 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb079_fresh_042 (A : Class) :
    (nb079AlphaDummy047 A) ∉
      (((synCcompl (Class.cv (nb079AlphaDummy038 A)))).fv ∪
        ((synCcompl (Class.cv (nb079AlphaDummy039 A)))).fv) :=
  by
  simpa only [nb079AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb079AlphaDummy038 A)))).fv ∪
        ((synCcompl (Class.cv (nb079AlphaDummy039 A)))).fv)
      0

theorem nb079_fresh_043 (x : Var) (y : Var) :
    (nb079AlphaDummy048 x y) ∉
      (((synCcompl (Class.cv (nb079AlphaDummy041 x y)))).fv ∪
        ((synCcompl (Class.cv (nb079AlphaDummy042 x y)))).fv) :=
  by
  simpa only [nb079AlphaDummy048] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb079AlphaDummy041 x y)))).fv ∪
        ((synCcompl (Class.cv (nb079AlphaDummy042 x y)))).fv)
      0

theorem nb079_fresh_044 (A : Class) :
    (nb079AlphaDummy055 A) ∉
      (((synCcompl (synCphi (Class.cv (nb079AlphaDummy024 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb079AlphaDummy055] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb079AlphaDummy024 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb079_fresh_045 (x : Var) (y : Var) :
    (nb079AlphaDummy056 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb079AlphaDummy026 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb079AlphaDummy056] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb079AlphaDummy026 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb079_fresh_046 (A : Class) :
    (nb079AlphaDummy015 A) ∉
      (((synCcompl (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb079AlphaDummy001 A))))).fv) :=
  by
  simpa only [nb079AlphaDummy015] using
    freshVar_not_mem
      (((synCcompl (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb079AlphaDummy001 A))))).fv)
      0

theorem nb079_fresh_047 (x : Var) (y : Var) :
    (nb079AlphaDummy016 x y) ∉
      (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv) :=
  by
  simpa only [nb079AlphaDummy016] using
    freshVar_not_mem
      (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv)
      0

theorem nb079_fresh_048 (A : Class) :
    (nb079AlphaDummy003 A) ∉
      (((synCcompl (synCsn (synCsn (Class.cv (nb079AlphaDummy000 A)))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
                (Class.cv (nb079AlphaDummy001 A)))))).fv) :=
  by
  simpa only [nb079AlphaDummy003] using
    freshVar_not_mem
      (((synCcompl (synCsn (synCsn (Class.cv (nb079AlphaDummy000 A)))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
                (Class.cv (nb079AlphaDummy001 A)))))).fv)
      0

theorem nb079_fresh_049 (x : Var) (y : Var) :
    (nb079AlphaDummy004 x y) ∉
      (((synCcompl (synCsn (synCsn (Class.cv x))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv x) (Class.cv y))))).fv) :=
  by
  simpa only [nb079AlphaDummy004] using
    freshVar_not_mem
      (((synCcompl (synCsn (synCsn (Class.cv x))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv x) (Class.cv y))))).fv)
      0

theorem nb079_fresh_050 (A : Class) :
    (nb079AlphaDummy043 A) ∉
      (((synCnin (Class.cv (nb079AlphaDummy038 A))
            (Class.cv (nb079AlphaDummy039 A)))).fv ∪
        ((synCnin (Class.cv (nb079AlphaDummy038 A))
            (Class.cv (nb079AlphaDummy039 A)))).fv) :=
  by
  simpa only [nb079AlphaDummy043] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb079AlphaDummy038 A))
            (Class.cv (nb079AlphaDummy039 A)))).fv ∪
        ((synCnin (Class.cv (nb079AlphaDummy038 A))
            (Class.cv (nb079AlphaDummy039 A)))).fv)
      0

theorem nb079_fresh_051 (x : Var) (y : Var) :
    (nb079AlphaDummy044 x y) ∉
      (((synCnin (Class.cv (nb079AlphaDummy041 x y))
            (Class.cv (nb079AlphaDummy042 x y)))).fv ∪
        ((synCnin (Class.cv (nb079AlphaDummy041 x y))
            (Class.cv (nb079AlphaDummy042 x y)))).fv) :=
  by
  simpa only [nb079AlphaDummy044] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb079AlphaDummy041 x y))
            (Class.cv (nb079AlphaDummy042 x y)))).fv ∪
        ((synCnin (Class.cv (nb079AlphaDummy041 x y))
            (Class.cv (nb079AlphaDummy042 x y)))).fv)
      0

theorem nb079_fresh_052 (A : Class) :
    (nb079AlphaDummy057 A) ∉
      (((synCphi (Class.cv (nb079AlphaDummy024 A)))).fv ∪
        ((synCphi (Class.cv (nb079AlphaDummy024 A)))).fv) :=
  by
  simpa only [nb079AlphaDummy057] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb079AlphaDummy024 A)))).fv ∪
        ((synCphi (Class.cv (nb079AlphaDummy024 A)))).fv)
      0

theorem nb079_fresh_053 (x : Var) (y : Var) :
    (nb079AlphaDummy058 x y) ∉
      (((synCphi (Class.cv (nb079AlphaDummy026 x y)))).fv ∪
        ((synCphi (Class.cv (nb079AlphaDummy026 x y)))).fv) :=
  by
  simpa only [nb079AlphaDummy058] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb079AlphaDummy026 x y)))).fv ∪
        ((synCphi (Class.cv (nb079AlphaDummy026 x y)))).fv)
      0

theorem nb079_fresh_054 (A : Class) :
    (nb079AlphaDummy013 A) ∉
      (((synCpr (Class.cv (nb079AlphaDummy000 A))
          (Class.cv (nb079AlphaDummy001 A)))).fv) :=
  by
  simpa only [nb079AlphaDummy013] using
    freshVar_not_mem
      (((synCpr (Class.cv (nb079AlphaDummy000 A)) (Class.cv (nb079AlphaDummy001 A)))).fv)
      0

theorem nb079_fresh_055 (x : Var) (y : Var) :
    (nb079AlphaDummy014 x y) ∉ (((synCpr (Class.cv x) (Class.cv y))).fv) := by
  simpa only [nb079AlphaDummy014] using
    freshVar_not_mem (((synCpr (Class.cv x) (Class.cv y))).fv) 0

theorem nb079_fresh_056 (A : Class) :
    (nb079AlphaDummy007 A) ∉ (((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb079AlphaDummy007] using
    freshVar_not_mem (((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv) 0

theorem nb079_fresh_057 (A : Class) :
    (nb079AlphaDummy017 A) ∉
      (((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv ∪
        ((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb079AlphaDummy017] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv ∪
        ((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv)
      0

theorem nb079_fresh_058 (A : Class) :
    (nb079AlphaDummy019 A) ∉
      (((synCsn (Class.cv (nb079AlphaDummy001 A)))).fv ∪
        ((synCsn (Class.cv (nb079AlphaDummy001 A)))).fv) :=
  by
  simpa only [nb079AlphaDummy019] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb079AlphaDummy001 A)))).fv ∪
        ((synCsn (Class.cv (nb079AlphaDummy001 A)))).fv)
      0

theorem nb079_fresh_059 (x : Var) :
    (nb079AlphaDummy008 x) ∉ (((synCsn (Class.cv x))).fv) := by
  simpa only [nb079AlphaDummy008] using
    freshVar_not_mem (((synCsn (Class.cv x))).fv) 0

theorem nb079_fresh_060 (x : Var) :
    (nb079AlphaDummy018 x) ∉
      (((synCsn (Class.cv x))).fv ∪ ((synCsn (Class.cv x))).fv) :=
  by
  simpa only [nb079AlphaDummy018] using
    freshVar_not_mem (((synCsn (Class.cv x))).fv ∪ ((synCsn (Class.cv x))).fv) 0

theorem nb079_fresh_061 (y : Var) :
    (nb079AlphaDummy020 y) ∉
      (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) :=
  by
  simpa only [nb079AlphaDummy020] using
    freshVar_not_mem (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) 0

theorem nb079_fresh_062 (A : Class) :
    (nb079AlphaDummy011 A) ∉
      (((synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))))).fv) :=
  by
  simpa only [nb079AlphaDummy011] using
    freshVar_not_mem
      (((synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))))).fv)
      0

theorem nb079_fresh_063 (x : Var) (y : Var) :
    (nb079AlphaDummy012 x y) ∉
      (((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv ∪
        ((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv) :=
  by
  simpa only [nb079AlphaDummy012] using
    freshVar_not_mem
      (((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv ∪
        ((synCsn (synCpr (Class.cv x) (Class.cv y)))).fv)
      0

theorem nb079_fresh_064 (A : Class) :
    (nb079AlphaDummy005 A) ∉
      (((synCsn (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv) :=
  by
  simpa only [nb079AlphaDummy005] using
    freshVar_not_mem
      (((synCsn (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv)
      0

theorem nb079_fresh_065 (x : Var) :
    (nb079AlphaDummy006 x) ∉
      (((synCsn (synCsn (Class.cv x)))).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) :=
  by
  simpa only [nb079AlphaDummy006] using
    freshVar_not_mem
      (((synCsn (synCsn (Class.cv x)))).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) 0

theorem nb079_fresh_066 (A : Class) : (nb079AlphaDummy000 A) ∉ ((A).fv) := by
  simpa only [nb079AlphaDummy000] using freshVar_not_mem ((A).fv) 0

theorem nb079_fresh_067 (A : Class) : (nb079AlphaDummy001 A) ∉ ((A).fv) := by
  simpa only [nb079AlphaDummy001] using freshVar_not_mem ((A).fv) 1

theorem nb079_fresh_068 (A : Class) : (nb079AlphaDummy002 A) ∉ ((A).fv) := by
  simpa only [nb079AlphaDummy002] using freshVar_not_mem ((A).fv) 2

theorem nb079_distinct_069 (A : Class) :
    (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy001 A) := by
  simpa only [nb079AlphaDummy000, nb079AlphaDummy001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb079_distinct_070 (A : Class) :
    (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy002 A) := by
  simpa only [nb079AlphaDummy000, nb079AlphaDummy002] using
    (freshVar_injective ((A).fv) (i := 0) (j := 2) (by decide))

theorem nb079_distinct_071 (A : Class) :
    (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy002 A) := by
  simpa only [nb079AlphaDummy001, nb079AlphaDummy002] using
    (freshVar_injective ((A).fv) (i := 1) (j := 2) (by decide))

theorem nb079_support_mem_0000 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((synCcompl (synCsn (synCsn (Class.cv (nb079AlphaDummy000 A)))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
                (Class.cv (nb079AlphaDummy001 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0001 (x : Var) (y : Var) :
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

theorem nb079_support_mem_0002 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((synCsn (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0003 (x : Var) :
    x ∈ (((synCsn (synCsn (Class.cv x)))).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0004 (A : Class) :
    (nb079AlphaDummy000 A) ∈ (((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0005 (x : Var) : x ∈ (((synCsn (Class.cv x))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0006 (A : Class) :
    (nb079AlphaDummy000 A) ∈ (((Class.cv (nb079AlphaDummy000 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0007 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0008 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0009 (x : Var) (y : Var) :
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

theorem nb079_support_mem_0010 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((synCpr (Class.cv (nb079AlphaDummy000 A))
          (Class.cv (nb079AlphaDummy001 A)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0011 (x : Var) (y : Var) :
    x ∈ (((synCpr (Class.cv x) (Class.cv y))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0012 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((synCcompl (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb079AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0013 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0014 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv ∪
        ((synCsn (Class.cv (nb079AlphaDummy000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0015 (x : Var) :
    x ∈ (((synCsn (Class.cv x))).fv ∪ ((synCsn (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0016 (A : Class) :
    (nb079AlphaDummy001 A) ∈
      (((synCcompl (synCsn (synCsn (Class.cv (nb079AlphaDummy000 A)))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
                (Class.cv (nb079AlphaDummy001 A)))))).fv) :=
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

theorem nb079_support_mem_0017 (x : Var) (y : Var) :
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

theorem nb079_support_mem_0018 (A : Class) :
    (nb079AlphaDummy001 A) ∈
      (((synCsn (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C079C001Part002`. -/


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

theorem nb079_support_mem_0019 (x : Var) (y : Var) :
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

theorem nb079_support_mem_0020 (A : Class) :
    (nb079AlphaDummy001 A) ∈
      (((synCpr (Class.cv (nb079AlphaDummy000 A))
          (Class.cv (nb079AlphaDummy001 A)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0021 (x : Var) (y : Var) :
    y ∈ (((synCpr (Class.cv x) (Class.cv y))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0022 (A : Class) :
    (nb079AlphaDummy001 A) ∈
      (((synCcompl (synCsn (Class.cv (nb079AlphaDummy000 A))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb079AlphaDummy001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0023 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (synCsn (Class.cv x)))).fv ∪ ((synCcompl (synCsn (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0024 (A : Class) :
    (nb079AlphaDummy001 A) ∈
      (((synCsn (Class.cv (nb079AlphaDummy001 A)))).fv ∪
        ((synCsn (Class.cv (nb079AlphaDummy001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0025 (y : Var) :
    y ∈ (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0026 (A : Class) :
    (nb079AlphaDummy001 A) ∈ (((Class.cv (nb079AlphaDummy001 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0027 (y : Var) : y ∈ (((Class.cv y)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0028 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((Class.cv (nb079AlphaDummy000 A))).fv ∪ ((Class.cv (nb079AlphaDummy001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0029 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((synCcompl (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCphi (Class.cv (nb079AlphaDummy024 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy023 A) from (by
          unfold nb079AlphaDummy023;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy024 A) from (by
            unfold nb079AlphaDummy024;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0030 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0031 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCphi (Class.cv (nb079AlphaDummy026 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb079AlphaDummy025 x y) from (by
          unfold nb079AlphaDummy025;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb079AlphaDummy026 x y) from (by
            unfold nb079AlphaDummy026;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0032 (A : Class) :
    (nb079AlphaDummy000 A) ∈
      (((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCphi (Class.cv (nb079AlphaDummy024 A))))))).fv ∪
        ((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCphi (Class.cv (nb079AlphaDummy024 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy023 A) from (by
          unfold nb079AlphaDummy023;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy024 A) from (by
            unfold nb079AlphaDummy024;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0033 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCphi (Class.cv (nb079AlphaDummy026 x y))))))).fv ∪
        ((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCphi (Class.cv (nb079AlphaDummy026 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb079AlphaDummy025 x y) from (by
          unfold nb079AlphaDummy025;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb079AlphaDummy026 x y) from (by
            unfold nb079AlphaDummy026;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0034 (A : Class) :
    (nb079AlphaDummy024 A) ∈ (((Class.cv (nb079AlphaDummy024 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0035 (x : Var) (y : Var) :
    (nb079AlphaDummy026 x y) ∈ (((Class.cv (nb079AlphaDummy026 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0036 (A : Class) :
    (nb079AlphaDummy031 A) ∈
      (((Wff.classMem (Class.cv (nb079AlphaDummy031 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb079AlphaDummy031 A)) (synC1c))).fv ∪
        ((Class.cv (nb079AlphaDummy031 A))).fv) :=
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

theorem nb079_support_mem_0037 (x : Var) (y : Var) :
    (nb079AlphaDummy033 x y) ∈
      (((Wff.classMem (Class.cv (nb079AlphaDummy033 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb079AlphaDummy033 x y)) (synC1c))).fv ∪
        ((Class.cv (nb079AlphaDummy033 x y))).fv) :=
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

theorem nb079_support_mem_0038 (A : Class) :
    (nb079AlphaDummy031 A) ∈
      (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0039 (x : Var) (y : Var) :
    (nb079AlphaDummy033 x y) ∈
      (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0040 (A : Class) :
    (nb079AlphaDummy038 A) ∈
      (((synCnin (Class.cv (nb079AlphaDummy038 A))
            (Class.cv (nb079AlphaDummy039 A)))).fv ∪
        ((synCnin (Class.cv (nb079AlphaDummy038 A))
            (Class.cv (nb079AlphaDummy039 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0041 (x : Var) (y : Var) :
    (nb079AlphaDummy041 x y) ∈
      (((synCnin (Class.cv (nb079AlphaDummy041 x y))
            (Class.cv (nb079AlphaDummy042 x y)))).fv ∪
        ((synCnin (Class.cv (nb079AlphaDummy041 x y))
            (Class.cv (nb079AlphaDummy042 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0042 (A : Class) :
    (nb079AlphaDummy038 A) ∈
      (((Class.cv (nb079AlphaDummy038 A))).fv ∪ ((Class.cv (nb079AlphaDummy039 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0043 (x : Var) (y : Var) :
    (nb079AlphaDummy041 x y) ∈
      (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy042 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0044 (A : Class) :
    (nb079AlphaDummy039 A) ∈
      (((synCnin (Class.cv (nb079AlphaDummy038 A))
            (Class.cv (nb079AlphaDummy039 A)))).fv ∪
        ((synCnin (Class.cv (nb079AlphaDummy038 A))
            (Class.cv (nb079AlphaDummy039 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0045 (x : Var) (y : Var) :
    (nb079AlphaDummy042 x y) ∈
      (((synCnin (Class.cv (nb079AlphaDummy041 x y))
            (Class.cv (nb079AlphaDummy042 x y)))).fv ∪
        ((synCnin (Class.cv (nb079AlphaDummy041 x y))
            (Class.cv (nb079AlphaDummy042 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0046 (A : Class) :
    (nb079AlphaDummy039 A) ∈
      (((Class.cv (nb079AlphaDummy038 A))).fv ∪ ((Class.cv (nb079AlphaDummy039 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0047 (x : Var) (y : Var) :
    (nb079AlphaDummy042 x y) ∈
      (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy042 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0048 (A : Class) :
    (nb079AlphaDummy038 A) ∈
      (((synCcompl (Class.cv (nb079AlphaDummy038 A)))).fv ∪
        ((synCcompl (Class.cv (nb079AlphaDummy039 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0049 (x : Var) (y : Var) :
    (nb079AlphaDummy041 x y) ∈
      (((synCcompl (Class.cv (nb079AlphaDummy041 x y)))).fv ∪
        ((synCcompl (Class.cv (nb079AlphaDummy042 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0050 (A : Class) :
    (nb079AlphaDummy038 A) ∈
      (((Class.cv (nb079AlphaDummy038 A))).fv ∪ ((Class.cv (nb079AlphaDummy038 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0051 (x : Var) (y : Var) :
    (nb079AlphaDummy041 x y) ∈
      (((Class.cv (nb079AlphaDummy041 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy041 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0052 (A : Class) :
    (nb079AlphaDummy039 A) ∈
      (((synCcompl (Class.cv (nb079AlphaDummy038 A)))).fv ∪
        ((synCcompl (Class.cv (nb079AlphaDummy039 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0053 (x : Var) (y : Var) :
    (nb079AlphaDummy042 x y) ∈
      (((synCcompl (Class.cv (nb079AlphaDummy041 x y)))).fv ∪
        ((synCcompl (Class.cv (nb079AlphaDummy042 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0054 (A : Class) :
    (nb079AlphaDummy039 A) ∈
      (((Class.cv (nb079AlphaDummy039 A))).fv ∪ ((Class.cv (nb079AlphaDummy039 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0055 (x : Var) (y : Var) :
    (nb079AlphaDummy042 x y) ∈
      (((Class.cv (nb079AlphaDummy042 x y))).fv ∪
        ((Class.cv (nb079AlphaDummy042 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0056 (A : Class) :
    (nb079AlphaDummy001 A) ∈
      (((Class.cv (nb079AlphaDummy000 A))).fv ∪ ((Class.cv (nb079AlphaDummy001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0057 (A : Class) :
    (nb079AlphaDummy001 A) ∈
      (((synCcompl (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy000 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCphi (Class.cv (nb079AlphaDummy024 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy023 A) from (by
          unfold nb079AlphaDummy023;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy024 A) from (by
            unfold nb079AlphaDummy024;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0058 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0059 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCphi (Class.cv (nb079AlphaDummy026 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb079AlphaDummy025 x y) from (by
          unfold nb079AlphaDummy025;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb079AlphaDummy026 x y) from (by
            unfold nb079AlphaDummy026;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0060 (A : Class) :
    (nb079AlphaDummy001 A) ∈
      (((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy023 A) from (by
          unfold nb079AlphaDummy023;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy024 A) from (by
            unfold nb079AlphaDummy024;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0061 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb079AlphaDummy025 x y) from (by
          unfold nb079AlphaDummy025;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb079AlphaDummy026 x y) from (by
            unfold nb079AlphaDummy026;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0062 (A : Class) :
    (nb079AlphaDummy024 A) ∈
      (((synCcompl (synCphi (Class.cv (nb079AlphaDummy024 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0063 (x : Var) (y : Var) :
    (nb079AlphaDummy026 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb079AlphaDummy026 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0064 (A : Class) :
    (nb079AlphaDummy024 A) ∈
      (((synCphi (Class.cv (nb079AlphaDummy024 A)))).fv ∪
        ((synCphi (Class.cv (nb079AlphaDummy024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0065 (x : Var) (y : Var) :
    (nb079AlphaDummy026 x y) ∈
      (((synCphi (Class.cv (nb079AlphaDummy026 x y)))).fv ∪
        ((synCphi (Class.cv (nb079AlphaDummy026 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
