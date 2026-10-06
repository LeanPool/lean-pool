/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C053C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_000`. -/
@[expose]
noncomputable def nb053AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_001`. -/
@[expose]
noncomputable def nb053AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_002`. -/
@[expose]
noncomputable def nb053AlphaDummy002 : Var :=
  (freshVar
    (({(nb053AlphaDummy000)} : Finset Var) ∪ ({(nb053AlphaDummy001)} : Finset Var) ∪
      ((Wff.classEq
          (synCin (Class.cv (nb053AlphaDummy000)) (Class.cv (nb053AlphaDummy001)))
          (synC0))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_003`. -/
@[expose]
noncomputable def nb053AlphaDummy003 (x : Var) (y : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((Wff.classEq (synCin (Class.cv x) (Class.cv y)) (synC0))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_004`. -/
@[expose]
noncomputable def nb053AlphaDummy004 : Var :=
  (freshVar
    (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_005`. -/
@[expose]
noncomputable def nb053AlphaDummy005 : Var :=
  (freshVar
    (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_006`. -/
@[expose]
noncomputable def nb053AlphaDummy006 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_007`. -/
@[expose]
noncomputable def nb053AlphaDummy007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_008`. -/
@[expose]
noncomputable def nb053AlphaDummy008 : Var :=
  (freshVar (((synCcompl (Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCphi (Class.cv (nb053AlphaDummy005)))))))).fv ∪ ((synCcompl
          (Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_009`. -/
@[expose]
noncomputable def nb053AlphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCphi (Class.cv (nb053AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_010`. -/
@[expose]
noncomputable def nb053AlphaDummy010 : Var :=
  (freshVar (((Class.cab (nb053AlphaDummy004)
          (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
            (Wff.classEq (Class.cv (nb053AlphaDummy004))
              (synCphi (Class.cv (nb053AlphaDummy005))))))).fv ∪
      ((Class.cab (nb053AlphaDummy004)
          (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
            (Wff.classEq (Class.cv (nb053AlphaDummy004))
              (synCphi (Class.cv (nb053AlphaDummy005))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_011`. -/
@[expose]
noncomputable def nb053AlphaDummy011 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb053AlphaDummy006 x y)
          (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
              (synCphi (Class.cv (nb053AlphaDummy007 x y))))))).fv ∪
      ((Class.cab (nb053AlphaDummy006 x y) (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
              (synCphi (Class.cv (nb053AlphaDummy007 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_012`. -/
@[expose]
noncomputable def nb053AlphaDummy012 : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy005))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_013`. -/
@[expose]
noncomputable def nb053AlphaDummy013 : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy005))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_014`. -/
@[expose]
noncomputable def nb053AlphaDummy014 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy007 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_015`. -/
@[expose]
noncomputable def nb053AlphaDummy015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy007 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_016`. -/
@[expose]
noncomputable def nb053AlphaDummy016 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb053AlphaDummy012)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb053AlphaDummy012)) (synC1c))).fv ∪
      ((Class.cv (nb053AlphaDummy012))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_017`. -/
@[expose]
noncomputable def nb053AlphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb053AlphaDummy014 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb053AlphaDummy014 x y)) (synC1c))).fv ∪
      ((Class.cv (nb053AlphaDummy014 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_018`. -/
@[expose]
noncomputable def nb053AlphaDummy018 : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_019`. -/
@[expose]
noncomputable def nb053AlphaDummy019 : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_020`. -/
@[expose]
noncomputable def nb053AlphaDummy020 : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_021`. -/
@[expose]
noncomputable def nb053AlphaDummy021 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_022`. -/
@[expose]
noncomputable def nb053AlphaDummy022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_023`. -/
@[expose]
noncomputable def nb053AlphaDummy023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_024`. -/
@[expose]
noncomputable def nb053AlphaDummy024 : Var :=
  (freshVar (((synCnin (Class.cv (nb053AlphaDummy019))
          (Class.cv (nb053AlphaDummy020)))).fv ∪
      ((synCnin (Class.cv (nb053AlphaDummy019)) (Class.cv (nb053AlphaDummy020)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_025`. -/
@[expose]
noncomputable def nb053AlphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb053AlphaDummy022 x y))
          (Class.cv (nb053AlphaDummy023 x y)))).fv ∪
      ((synCnin (Class.cv (nb053AlphaDummy022 x y))
          (Class.cv (nb053AlphaDummy023 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_026`. -/
@[expose]
noncomputable def nb053AlphaDummy026 : Var :=
  (freshVar
    (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_027`. -/
@[expose]
noncomputable def nb053AlphaDummy027 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
      ((Class.cv (nb053AlphaDummy023 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_028`. -/
@[expose]
noncomputable def nb053AlphaDummy028 : Var :=
  (freshVar (((synCcompl (Class.cv (nb053AlphaDummy019)))).fv ∪
      ((synCcompl (Class.cv (nb053AlphaDummy020)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_029`. -/
@[expose]
noncomputable def nb053AlphaDummy029 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb053AlphaDummy022 x y)))).fv ∪
      ((synCcompl (Class.cv (nb053AlphaDummy023 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_030`. -/
@[expose]
noncomputable def nb053AlphaDummy030 : Var :=
  (freshVar
    (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy019))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_031`. -/
@[expose]
noncomputable def nb053AlphaDummy031 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
      ((Class.cv (nb053AlphaDummy022 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_032`. -/
@[expose]
noncomputable def nb053AlphaDummy032 : Var :=
  (freshVar
    (((Class.cv (nb053AlphaDummy020))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_033`. -/
@[expose]
noncomputable def nb053AlphaDummy033 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb053AlphaDummy023 x y))).fv ∪
      ((Class.cv (nb053AlphaDummy023 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_034`. -/
@[expose]
noncomputable def nb053AlphaDummy034 : Var :=
  (freshVar (((Class.cab (nb053AlphaDummy004)
          (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
            (Wff.classEq (Class.cv (nb053AlphaDummy004))
              (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb053AlphaDummy004)
          (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
            (Wff.classEq (Class.cv (nb053AlphaDummy004))
              (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_035`. -/
@[expose]
noncomputable def nb053AlphaDummy035 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb053AlphaDummy006 x y)
          (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
              (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb053AlphaDummy006 x y)
          (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
              (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_036`. -/
@[expose]
noncomputable def nb053AlphaDummy036 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb053AlphaDummy005))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_037`. -/
@[expose]
noncomputable def nb053AlphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb053AlphaDummy007 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_038`. -/
@[expose]
noncomputable def nb053AlphaDummy038 : Var :=
  (freshVar (((synCphi (Class.cv (nb053AlphaDummy005)))).fv ∪
      ((synCphi (Class.cv (nb053AlphaDummy005)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_039`. -/
@[expose]
noncomputable def nb053AlphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb053AlphaDummy007 x y)))).fv ∪
      ((synCphi (Class.cv (nb053AlphaDummy007 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_040`. -/
@[expose]
noncomputable def nb053AlphaDummy040 : Var :=
  (freshVar (((synCnin (Class.cv (nb053AlphaDummy000))
          (Class.cv (nb053AlphaDummy001)))).fv ∪
      ((synCnin (Class.cv (nb053AlphaDummy000)) (Class.cv (nb053AlphaDummy001)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb053_alpha_dummy_041`. -/
@[expose]
noncomputable def nb053AlphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv x) (Class.cv y))).fv ∪
      ((synCnin (Class.cv x) (Class.cv y))).fv) 0)

theorem nb053_fresh_000 :
    (nb053AlphaDummy010) ∉
      (((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCphi (Class.cv (nb053AlphaDummy005))))))).fv ∪
        ((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCphi (Class.cv (nb053AlphaDummy005))))))).fv) :=
  by
  simpa only [nb053AlphaDummy010] using
    freshVar_not_mem
      (((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCphi (Class.cv (nb053AlphaDummy005))))))).fv ∪
        ((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCphi (Class.cv (nb053AlphaDummy005))))))).fv)
      0

theorem nb053_fresh_001 :
    (nb053AlphaDummy034) ∉
      (((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb053AlphaDummy034] using
    freshVar_not_mem
      (((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb053_fresh_002 (x : Var) (y : Var) :
    (nb053AlphaDummy011 x y) ∉
      (((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCphi (Class.cv (nb053AlphaDummy007 x y))))))).fv ∪
        ((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCphi (Class.cv (nb053AlphaDummy007 x y))))))).fv) :=
  by
  simpa only [nb053AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCphi (Class.cv (nb053AlphaDummy007 x y))))))).fv ∪
        ((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCphi (Class.cv (nb053AlphaDummy007 x y))))))).fv)
      0

theorem nb053_fresh_003 (x : Var) (y : Var) :
    (nb053AlphaDummy035 x y) ∉
      (((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb053AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb053_fresh_004 :
    (nb053AlphaDummy004) ∉
      (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv) :=
  by
  simpa only [nb053AlphaDummy004] using
    freshVar_not_mem
      (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv)
      0

theorem nb053_fresh_005 :
    (nb053AlphaDummy005) ∉
      (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv) :=
  by
  simpa only [nb053AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv)
      1

theorem nb053_distinct_006 : (nb053AlphaDummy004) ≠ (nb053AlphaDummy005) := by
  simpa only [nb053AlphaDummy004, nb053AlphaDummy005] using
    (freshVar_injective
      (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb053_fresh_007 :
    (nb053AlphaDummy012) ∉ (((Class.cv (nb053AlphaDummy005))).fv) := by
  simpa only [nb053AlphaDummy012] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy005))).fv) 0

theorem nb053_fresh_008 :
    (nb053AlphaDummy013) ∉ (((Class.cv (nb053AlphaDummy005))).fv) := by
  simpa only [nb053AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy005))).fv) 1

theorem nb053_distinct_009 : (nb053AlphaDummy012) ≠ (nb053AlphaDummy013) := by
  simpa only [nb053AlphaDummy012, nb053AlphaDummy013] using
    (freshVar_injective (((Class.cv (nb053AlphaDummy005))).fv) (i := 0) (j := 1) (by decide))

theorem nb053_fresh_010 (x : Var) (y : Var) :
    (nb053AlphaDummy014 x y) ∉ (((Class.cv (nb053AlphaDummy007 x y))).fv) := by
  simpa only [nb053AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy007 x y))).fv) 0

theorem nb053_fresh_011 (x : Var) (y : Var) :
    (nb053AlphaDummy015 x y) ∉ (((Class.cv (nb053AlphaDummy007 x y))).fv) := by
  simpa only [nb053AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy007 x y))).fv) 1

theorem nb053_distinct_012 (x : Var) (y : Var) :
    (nb053AlphaDummy014 x y) ≠ (nb053AlphaDummy015 x y) := by
  simpa only [nb053AlphaDummy014, nb053AlphaDummy015] using
    (freshVar_injective (((Class.cv (nb053AlphaDummy007 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb053_fresh_013 :
    (nb053AlphaDummy018) ∉
      (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb053AlphaDummy018] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) 0

theorem nb053_fresh_014 :
    (nb053AlphaDummy019) ∉
      (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb053AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) 1

theorem nb053_fresh_015 :
    (nb053AlphaDummy020) ∉
      (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb053AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) 2

theorem nb053_distinct_016 : (nb053AlphaDummy018) ≠ (nb053AlphaDummy019) := by
  simpa only [nb053AlphaDummy018, nb053AlphaDummy019] using
    (freshVar_injective (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb053_distinct_017 : (nb053AlphaDummy018) ≠ (nb053AlphaDummy020) := by
  simpa only [nb053AlphaDummy018, nb053AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb053_distinct_018 : (nb053AlphaDummy019) ≠ (nb053AlphaDummy020) := by
  simpa only [nb053AlphaDummy019, nb053AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb053_fresh_019 (x : Var) (y : Var) :
    (nb053AlphaDummy021 x y) ∉
      (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb053AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb053_fresh_020 (x : Var) (y : Var) :
    (nb053AlphaDummy022 x y) ∉
      (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb053AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb053_fresh_021 (x : Var) (y : Var) :
    (nb053AlphaDummy023 x y) ∉
      (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb053AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb053_distinct_022 (x : Var) (y : Var) :
    (nb053AlphaDummy021 x y) ≠ (nb053AlphaDummy022 x y) := by
  simpa only [nb053AlphaDummy021, nb053AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb053_distinct_023 (x : Var) (y : Var) :
    (nb053AlphaDummy021 x y) ≠ (nb053AlphaDummy023 x y) := by
  simpa only [nb053AlphaDummy021, nb053AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb053_distinct_024 (x : Var) (y : Var) :
    (nb053AlphaDummy022 x y) ≠ (nb053AlphaDummy023 x y) := by
  simpa only [nb053AlphaDummy022, nb053AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb053_fresh_025 :
    (nb053AlphaDummy030) ∉
      (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy019))).fv) :=
  by
  simpa only [nb053AlphaDummy030] using
    freshVar_not_mem
      (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy019))).fv)
      0

theorem nb053_fresh_026 :
    (nb053AlphaDummy026) ∉
      (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv) :=
  by
  simpa only [nb053AlphaDummy026] using
    freshVar_not_mem
      (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv)
      0

theorem nb053_fresh_027 :
    (nb053AlphaDummy032) ∉
      (((Class.cv (nb053AlphaDummy020))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv) :=
  by
  simpa only [nb053AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb053AlphaDummy020))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv)
      0

theorem nb053_fresh_028 (x : Var) (y : Var) :
    (nb053AlphaDummy031 x y) ∉
      (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy022 x y))).fv) :=
  by
  simpa only [nb053AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy022 x y))).fv)
      0

theorem nb053_fresh_029 (x : Var) (y : Var) :
    (nb053AlphaDummy027 x y) ∉
      (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy023 x y))).fv) :=
  by
  simpa only [nb053AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy023 x y))).fv)
      0

theorem nb053_fresh_030 (x : Var) (y : Var) :
    (nb053AlphaDummy033 x y) ∉
      (((Class.cv (nb053AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy023 x y))).fv) :=
  by
  simpa only [nb053AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb053AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy023 x y))).fv)
      0

theorem nb053_fresh_031 (x : Var) (y : Var) :
    (nb053AlphaDummy006 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb053AlphaDummy006] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb053_fresh_032 (x : Var) (y : Var) :
    (nb053AlphaDummy007 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb053AlphaDummy007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb053_distinct_033 (x : Var) (y : Var) :
    (nb053AlphaDummy006 x y) ≠ (nb053AlphaDummy007 x y) := by
  simpa only [nb053AlphaDummy006, nb053AlphaDummy007] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb053_fresh_034 :
    (nb053AlphaDummy016) ∉
      (((Wff.classMem (Class.cv (nb053AlphaDummy012)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb053AlphaDummy012)) (synC1c))).fv ∪
        ((Class.cv (nb053AlphaDummy012))).fv) :=
  by
  simpa only [nb053AlphaDummy016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb053AlphaDummy012)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb053AlphaDummy012)) (synC1c))).fv ∪
        ((Class.cv (nb053AlphaDummy012))).fv)
      0

theorem nb053_fresh_035 (x : Var) (y : Var) :
    (nb053AlphaDummy017 x y) ∉
      (((Wff.classMem (Class.cv (nb053AlphaDummy014 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb053AlphaDummy014 x y)) (synC1c))).fv ∪
        ((Class.cv (nb053AlphaDummy014 x y))).fv) :=
  by
  simpa only [nb053AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb053AlphaDummy014 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb053AlphaDummy014 x y)) (synC1c))).fv ∪
        ((Class.cv (nb053AlphaDummy014 x y))).fv)
      0

theorem nb053_fresh_036 :
    (nb053AlphaDummy008) ∉
      (((synCcompl (Class.cab (nb053AlphaDummy004)
              (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
                (Wff.classEq (Class.cv (nb053AlphaDummy004))
                  (synCphi (Class.cv (nb053AlphaDummy005)))))))).fv ∪ ((synCcompl
            (Class.cab (nb053AlphaDummy004)
              (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
                (Wff.classEq (Class.cv (nb053AlphaDummy004))
                  (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb053AlphaDummy008] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb053AlphaDummy004)
              (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
                (Wff.classEq (Class.cv (nb053AlphaDummy004))
                  (synCphi (Class.cv (nb053AlphaDummy005)))))))).fv ∪ ((synCcompl
            (Class.cab (nb053AlphaDummy004)
              (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
                (Wff.classEq (Class.cv (nb053AlphaDummy004))
                  (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb053_fresh_037 (x : Var) (y : Var) :
    (nb053AlphaDummy009 x y) ∉
      (((synCcompl (Class.cab (nb053AlphaDummy006 x y)
              (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                  (synCphi (Class.cv (nb053AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb053AlphaDummy006 x y)
              (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb053AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb053AlphaDummy006 x y)
              (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                  (synCphi (Class.cv (nb053AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb053AlphaDummy006 x y)
              (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb053_fresh_038 :
    (nb053AlphaDummy028) ∉
      (((synCcompl (Class.cv (nb053AlphaDummy019)))).fv ∪
        ((synCcompl (Class.cv (nb053AlphaDummy020)))).fv) :=
  by
  simpa only [nb053AlphaDummy028] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb053AlphaDummy019)))).fv ∪
        ((synCcompl (Class.cv (nb053AlphaDummy020)))).fv)
      0

theorem nb053_fresh_039 (x : Var) (y : Var) :
    (nb053AlphaDummy029 x y) ∉
      (((synCcompl (Class.cv (nb053AlphaDummy022 x y)))).fv ∪
        ((synCcompl (Class.cv (nb053AlphaDummy023 x y)))).fv) :=
  by
  simpa only [nb053AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb053AlphaDummy022 x y)))).fv ∪
        ((synCcompl (Class.cv (nb053AlphaDummy023 x y)))).fv)
      0

theorem nb053_fresh_040 :
    (nb053AlphaDummy036) ∉
      (((synCcompl (synCphi (Class.cv (nb053AlphaDummy005))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb053AlphaDummy036] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb053AlphaDummy005))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb053_fresh_041 (x : Var) (y : Var) :
    (nb053AlphaDummy037 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb053AlphaDummy007 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb053AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb053AlphaDummy007 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb053_fresh_042 :
    (nb053AlphaDummy040) ∉
      (((synCnin (Class.cv (nb053AlphaDummy000)) (Class.cv (nb053AlphaDummy001)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy000))
            (Class.cv (nb053AlphaDummy001)))).fv) :=
  by
  simpa only [nb053AlphaDummy040] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb053AlphaDummy000)) (Class.cv (nb053AlphaDummy001)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy000)) (Class.cv (nb053AlphaDummy001)))).fv)
      0

theorem nb053_fresh_043 :
    (nb053AlphaDummy024) ∉
      (((synCnin (Class.cv (nb053AlphaDummy019)) (Class.cv (nb053AlphaDummy020)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy019))
            (Class.cv (nb053AlphaDummy020)))).fv) :=
  by
  simpa only [nb053AlphaDummy024] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb053AlphaDummy019)) (Class.cv (nb053AlphaDummy020)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy019)) (Class.cv (nb053AlphaDummy020)))).fv)
      0

theorem nb053_fresh_044 (x : Var) (y : Var) :
    (nb053AlphaDummy025 x y) ∉
      (((synCnin (Class.cv (nb053AlphaDummy022 x y))
            (Class.cv (nb053AlphaDummy023 x y)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy022 x y))
            (Class.cv (nb053AlphaDummy023 x y)))).fv) :=
  by
  simpa only [nb053AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb053AlphaDummy022 x y))
            (Class.cv (nb053AlphaDummy023 x y)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy022 x y))
            (Class.cv (nb053AlphaDummy023 x y)))).fv)
      0

theorem nb053_fresh_045 (x : Var) (y : Var) :
    (nb053AlphaDummy041 x y) ∉
      (((synCnin (Class.cv x) (Class.cv y))).fv ∪ ((synCnin (Class.cv x) (Class.cv y))).fv) :=
  by
  simpa only [nb053AlphaDummy041] using
    freshVar_not_mem
      (((synCnin (Class.cv x) (Class.cv y))).fv ∪ ((synCnin (Class.cv x) (Class.cv y))).fv)
      0

theorem nb053_fresh_046 :
    (nb053AlphaDummy038) ∉
      (((synCphi (Class.cv (nb053AlphaDummy005)))).fv ∪
        ((synCphi (Class.cv (nb053AlphaDummy005)))).fv) :=
  by
  simpa only [nb053AlphaDummy038] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb053AlphaDummy005)))).fv ∪
        ((synCphi (Class.cv (nb053AlphaDummy005)))).fv)
      0

theorem nb053_fresh_047 (x : Var) (y : Var) :
    (nb053AlphaDummy039 x y) ∉
      (((synCphi (Class.cv (nb053AlphaDummy007 x y)))).fv ∪
        ((synCphi (Class.cv (nb053AlphaDummy007 x y)))).fv) :=
  by
  simpa only [nb053AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb053AlphaDummy007 x y)))).fv ∪
        ((synCphi (Class.cv (nb053AlphaDummy007 x y)))).fv)
      0

theorem nb053_fresh_048 :
    (nb053AlphaDummy002) ∉
      (({(nb053AlphaDummy000)} : Finset Var) ∪ ({(nb053AlphaDummy001)} : Finset Var) ∪
        ((Wff.classEq (synCin (Class.cv (nb053AlphaDummy000))
              (Class.cv (nb053AlphaDummy001))) (synC0))).fv) :=
  by
  simpa only [nb053AlphaDummy002] using
    freshVar_not_mem
      (({(nb053AlphaDummy000)} : Finset Var) ∪ ({(nb053AlphaDummy001)} : Finset Var) ∪
        ((Wff.classEq (synCin (Class.cv (nb053AlphaDummy000))
              (Class.cv (nb053AlphaDummy001))) (synC0))).fv)
      0

theorem nb053_fresh_049 (x : Var) (y : Var) :
    (nb053AlphaDummy003 x y) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classEq (synCin (Class.cv x) (Class.cv y)) (synC0))).fv) :=
  by
  simpa only [nb053AlphaDummy003] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classEq (synCin (Class.cv x) (Class.cv y)) (synC0))).fv)
      0

theorem nb053_fresh_050 : (nb053AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb053AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb053_fresh_051 : (nb053AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb053AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb053_distinct_052 : (nb053AlphaDummy000) ≠ (nb053AlphaDummy001) := by
  simpa only [nb053AlphaDummy000, nb053AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb053_support_mem_0000 :
    (nb053AlphaDummy000) ∈
      (({(nb053AlphaDummy000)} : Finset Var) ∪ ({(nb053AlphaDummy001)} : Finset Var) ∪
        ((Wff.classEq (synCin (Class.cv (nb053AlphaDummy000))
              (Class.cv (nb053AlphaDummy001))) (synC0))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0001 (x : Var) (y : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classEq (synCin (Class.cv x) (Class.cv y)) (synC0))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0002 :
    (nb053AlphaDummy001) ∈
      (({(nb053AlphaDummy000)} : Finset Var) ∪ ({(nb053AlphaDummy001)} : Finset Var) ∪
        ((Wff.classEq (synCin (Class.cv (nb053AlphaDummy000))
              (Class.cv (nb053AlphaDummy001))) (synC0))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0003 (x : Var) (y : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((Wff.classEq (synCin (Class.cv x) (Class.cv y)) (synC0))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0004 :
    (nb053AlphaDummy000) ∈
      (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0005 :
    (nb053AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb053AlphaDummy004)
              (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
                (Wff.classEq (Class.cv (nb053AlphaDummy004))
                  (synCphi (Class.cv (nb053AlphaDummy005)))))))).fv ∪ ((synCcompl
            (Class.cab (nb053AlphaDummy004)
              (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
                (Wff.classEq (Class.cv (nb053AlphaDummy004))
                  (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0006 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb053AlphaDummy006 x y)
              (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                  (synCphi (Class.cv (nb053AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb053AlphaDummy006 x y)
              (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0008 :
    (nb053AlphaDummy000) ∈
      (((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCphi (Class.cv (nb053AlphaDummy005))))))).fv ∪
        ((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCphi (Class.cv (nb053AlphaDummy005))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCphi (Class.cv (nb053AlphaDummy007 x y))))))).fv ∪
        ((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCphi (Class.cv (nb053AlphaDummy007 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0010 :
    (nb053AlphaDummy005) ∈ (((Class.cv (nb053AlphaDummy005))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0011 (x : Var) (y : Var) :
    (nb053AlphaDummy007 x y) ∈ (((Class.cv (nb053AlphaDummy007 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0012 :
    (nb053AlphaDummy012) ∈
      (((Wff.classMem (Class.cv (nb053AlphaDummy012)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb053AlphaDummy012)) (synC1c))).fv ∪
        ((Class.cv (nb053AlphaDummy012))).fv) :=
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

theorem nb053_support_mem_0013 (x : Var) (y : Var) :
    (nb053AlphaDummy014 x y) ∈
      (((Wff.classMem (Class.cv (nb053AlphaDummy014 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb053AlphaDummy014 x y)) (synC1c))).fv ∪
        ((Class.cv (nb053AlphaDummy014 x y))).fv) :=
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

theorem nb053_support_mem_0014 :
    (nb053AlphaDummy012) ∈
      (((Class.cv (nb053AlphaDummy012))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0015 (x : Var) (y : Var) :
    (nb053AlphaDummy014 x y) ∈
      (((Class.cv (nb053AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0016 :
    (nb053AlphaDummy019) ∈
      (((synCnin (Class.cv (nb053AlphaDummy019)) (Class.cv (nb053AlphaDummy020)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy019))
            (Class.cv (nb053AlphaDummy020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0017 (x : Var) (y : Var) :
    (nb053AlphaDummy022 x y) ∈
      (((synCnin (Class.cv (nb053AlphaDummy022 x y))
            (Class.cv (nb053AlphaDummy023 x y)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy022 x y))
            (Class.cv (nb053AlphaDummy023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0018 :
    (nb053AlphaDummy019) ∈
      (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0019 (x : Var) (y : Var) :
    (nb053AlphaDummy022 x y) ∈
      (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0020 :
    (nb053AlphaDummy020) ∈
      (((synCnin (Class.cv (nb053AlphaDummy019)) (Class.cv (nb053AlphaDummy020)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy019))
            (Class.cv (nb053AlphaDummy020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0021 (x : Var) (y : Var) :
    (nb053AlphaDummy023 x y) ∈
      (((synCnin (Class.cv (nb053AlphaDummy022 x y))
            (Class.cv (nb053AlphaDummy023 x y)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy022 x y))
            (Class.cv (nb053AlphaDummy023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0022 :
    (nb053AlphaDummy020) ∈
      (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0023 (x : Var) (y : Var) :
    (nb053AlphaDummy023 x y) ∈
      (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0024 :
    (nb053AlphaDummy019) ∈
      (((synCcompl (Class.cv (nb053AlphaDummy019)))).fv ∪
        ((synCcompl (Class.cv (nb053AlphaDummy020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0025 (x : Var) (y : Var) :
    (nb053AlphaDummy022 x y) ∈
      (((synCcompl (Class.cv (nb053AlphaDummy022 x y)))).fv ∪
        ((synCcompl (Class.cv (nb053AlphaDummy023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0026 :
    (nb053AlphaDummy019) ∈
      (((Class.cv (nb053AlphaDummy019))).fv ∪ ((Class.cv (nb053AlphaDummy019))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0027 (x : Var) (y : Var) :
    (nb053AlphaDummy022 x y) ∈
      (((Class.cv (nb053AlphaDummy022 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy022 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0028 :
    (nb053AlphaDummy020) ∈
      (((synCcompl (Class.cv (nb053AlphaDummy019)))).fv ∪
        ((synCcompl (Class.cv (nb053AlphaDummy020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0029 (x : Var) (y : Var) :
    (nb053AlphaDummy023 x y) ∈
      (((synCcompl (Class.cv (nb053AlphaDummy022 x y)))).fv ∪
        ((synCcompl (Class.cv (nb053AlphaDummy023 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0030 :
    (nb053AlphaDummy020) ∈
      (((Class.cv (nb053AlphaDummy020))).fv ∪ ((Class.cv (nb053AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0031 (x : Var) (y : Var) :
    (nb053AlphaDummy023 x y) ∈
      (((Class.cv (nb053AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb053AlphaDummy023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0032 :
    (nb053AlphaDummy001) ∈
      (((Class.cv (nb053AlphaDummy000))).fv ∪ ((Class.cv (nb053AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0033 :
    (nb053AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb053AlphaDummy004)
              (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy000))
                (Wff.classEq (Class.cv (nb053AlphaDummy004))
                  (synCphi (Class.cv (nb053AlphaDummy005)))))))).fv ∪ ((synCcompl
            (Class.cab (nb053AlphaDummy004)
              (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
                (Wff.classEq (Class.cv (nb053AlphaDummy004))
                  (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0034 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0035 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb053AlphaDummy006 x y)
              (synWrex (nb053AlphaDummy007 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                  (synCphi (Class.cv (nb053AlphaDummy007 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb053AlphaDummy006 x y)
              (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0034 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0034 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0036 :
    (nb053AlphaDummy001) ∈
      (((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb053AlphaDummy004)
            (synWrex (nb053AlphaDummy005) (Class.cv (nb053AlphaDummy001))
              (Wff.classEq (Class.cv (nb053AlphaDummy004))
                (synCun (synCphi (Class.cv (nb053AlphaDummy005)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0037 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb053AlphaDummy006 x y)
            (synWrex (nb053AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb053AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb053AlphaDummy007 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0034 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0034 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb053_support_mem_0038 :
    (nb053AlphaDummy005) ∈
      (((synCcompl (synCphi (Class.cv (nb053AlphaDummy005))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0039 (x : Var) (y : Var) :
    (nb053AlphaDummy007 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb053AlphaDummy007 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0040 :
    (nb053AlphaDummy005) ∈
      (((synCphi (Class.cv (nb053AlphaDummy005)))).fv ∪
        ((synCphi (Class.cv (nb053AlphaDummy005)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0041 (x : Var) (y : Var) :
    (nb053AlphaDummy007 x y) ∈
      (((synCphi (Class.cv (nb053AlphaDummy007 x y)))).fv ∪
        ((synCphi (Class.cv (nb053AlphaDummy007 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0042 :
    (nb053AlphaDummy000) ∈
      (((synCnin (Class.cv (nb053AlphaDummy000)) (Class.cv (nb053AlphaDummy001)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy000))
            (Class.cv (nb053AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0043 (x : Var) (y : Var) :
    x ∈
      (((synCnin (Class.cv x) (Class.cv y))).fv ∪ ((synCnin (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0044 :
    (nb053AlphaDummy001) ∈
      (((synCnin (Class.cv (nb053AlphaDummy000)) (Class.cv (nb053AlphaDummy001)))).fv ∪
        ((synCnin (Class.cv (nb053AlphaDummy000))
            (Class.cv (nb053AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb053_support_mem_0045 (x : Var) (y : Var) :
    y ∈
      (((synCnin (Class.cv x) (Class.cv y))).fv ∪ ((synCnin (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
