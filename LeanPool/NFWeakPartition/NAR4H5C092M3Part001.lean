/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4H5C092M3Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_000`. -/
@[expose]
noncomputable def nb092AlphaDummy000 (R : Class) : Var :=
  (freshVar ((R).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_001`. -/
@[expose]
noncomputable def nb092AlphaDummy001 (R : Class) : Var :=
  (freshVar ((R).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_002`. -/
@[expose]
noncomputable def nb092AlphaDummy002 (R : Class) : Var :=
  (freshVar ((R).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_003`. -/
@[expose]
noncomputable def nb092AlphaDummy003 (R : Class) : Var :=
  (freshVar ((R).fv) 3)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_004`. -/
@[expose]
noncomputable def nb092AlphaDummy004 (R : Class) : Var :=
  (freshVar (({(nb092AlphaDummy000 R)} : Finset Var) ∪
        ({(nb092AlphaDummy001 R)} : Finset Var) ∪
      ((synWrex (nb092AlphaDummy002 R) (Class.cv (nb092AlphaDummy000 R))
          (synWrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
            (synWbr (Class.cv (nb092AlphaDummy002 R)) R
              (Class.cv (nb092AlphaDummy003 R)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_005`. -/
@[expose]
noncomputable def nb092AlphaDummy005 (x : Var) (y : Var) (R : Class) (a : Var)
    (b : Var) : Var :=
  (freshVar (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
          (synWrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_006`. -/
@[expose]
noncomputable def nb092AlphaDummy006 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy000 R))).fv ∪
      ((Class.cv (nb092AlphaDummy001 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_007`. -/
@[expose]
noncomputable def nb092AlphaDummy007 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy000 R))).fv ∪
      ((Class.cv (nb092AlphaDummy001 R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_008`. -/
@[expose]
noncomputable def nb092AlphaDummy008 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_009`. -/
@[expose]
noncomputable def nb092AlphaDummy009 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_010`. -/
@[expose]
noncomputable def nb092AlphaDummy010 (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCphi (Class.cv (nb092AlphaDummy007 R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_011`. -/
@[expose]
noncomputable def nb092AlphaDummy011 (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCphi (Class.cv (nb092AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
          (Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_012`. -/
@[expose]
noncomputable def nb092AlphaDummy012 (R : Class) : Var :=
  (freshVar (((Class.cab (nb092AlphaDummy006 R)
          (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
            (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
              (synCphi (Class.cv (nb092AlphaDummy007 R))))))).fv ∪
      ((Class.cab (nb092AlphaDummy006 R)
          (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
            (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
              (synCphi (Class.cv (nb092AlphaDummy007 R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_013`. -/
@[expose]
noncomputable def nb092AlphaDummy013 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb092AlphaDummy008 a b)
          (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
              (synCphi (Class.cv (nb092AlphaDummy009 a b))))))).fv ∪
      ((Class.cab (nb092AlphaDummy008 a b) (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
              (synCphi (Class.cv (nb092AlphaDummy009 a b))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_014`. -/
@[expose]
noncomputable def nb092AlphaDummy014 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy007 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_015`. -/
@[expose]
noncomputable def nb092AlphaDummy015 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy007 R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_016`. -/
@[expose]
noncomputable def nb092AlphaDummy016 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy009 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_017`. -/
@[expose]
noncomputable def nb092AlphaDummy017 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy009 a b))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_018`. -/
@[expose]
noncomputable def nb092AlphaDummy018 (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb092AlphaDummy014 R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb092AlphaDummy014 R)) (synC1c))).fv ∪
      ((Class.cv (nb092AlphaDummy014 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_019`. -/
@[expose]
noncomputable def nb092AlphaDummy019 (a : Var) (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb092AlphaDummy016 a b)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb092AlphaDummy016 a b)) (synC1c))).fv ∪
      ((Class.cv (nb092AlphaDummy016 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_020`. -/
@[expose]
noncomputable def nb092AlphaDummy020 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_021`. -/
@[expose]
noncomputable def nb092AlphaDummy021 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_022`. -/
@[expose]
noncomputable def nb092AlphaDummy022 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_023`. -/
@[expose]
noncomputable def nb092AlphaDummy023 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_024`. -/
@[expose]
noncomputable def nb092AlphaDummy024 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_025`. -/
@[expose]
noncomputable def nb092AlphaDummy025 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_026`. -/
@[expose]
noncomputable def nb092AlphaDummy026 (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb092AlphaDummy021 R))
          (Class.cv (nb092AlphaDummy022 R)))).fv ∪
      ((synCnin (Class.cv (nb092AlphaDummy021 R)) (Class.cv (nb092AlphaDummy022 R)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_027`. -/
@[expose]
noncomputable def nb092AlphaDummy027 (a : Var) (b : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb092AlphaDummy024 a b))
          (Class.cv (nb092AlphaDummy025 a b)))).fv ∪
      ((synCnin (Class.cv (nb092AlphaDummy024 a b))
          (Class.cv (nb092AlphaDummy025 a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_028`. -/
@[expose]
noncomputable def nb092AlphaDummy028 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy021 R))).fv ∪
      ((Class.cv (nb092AlphaDummy022 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_029`. -/
@[expose]
noncomputable def nb092AlphaDummy029 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
      ((Class.cv (nb092AlphaDummy025 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_030`. -/
@[expose]
noncomputable def nb092AlphaDummy030 (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb092AlphaDummy021 R)))).fv ∪
      ((synCcompl (Class.cv (nb092AlphaDummy022 R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_031`. -/
@[expose]
noncomputable def nb092AlphaDummy031 (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb092AlphaDummy024 a b)))).fv ∪
      ((synCcompl (Class.cv (nb092AlphaDummy025 a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_032`. -/
@[expose]
noncomputable def nb092AlphaDummy032 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy021 R))).fv ∪
      ((Class.cv (nb092AlphaDummy021 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_033`. -/
@[expose]
noncomputable def nb092AlphaDummy033 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
      ((Class.cv (nb092AlphaDummy024 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_034`. -/
@[expose]
noncomputable def nb092AlphaDummy034 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy022 R))).fv ∪
      ((Class.cv (nb092AlphaDummy022 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_035`. -/
@[expose]
noncomputable def nb092AlphaDummy035 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy025 a b))).fv ∪
      ((Class.cv (nb092AlphaDummy025 a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_036`. -/
@[expose]
noncomputable def nb092AlphaDummy036 (R : Class) : Var :=
  (freshVar (((Class.cab (nb092AlphaDummy006 R)
          (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
            (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
              (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy006 R)
          (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
            (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
              (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_037`. -/
@[expose]
noncomputable def nb092AlphaDummy037 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb092AlphaDummy008 a b)
          (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
            (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
              (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy008 a b)
          (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
            (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
              (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_038`. -/
@[expose]
noncomputable def nb092AlphaDummy038 (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb092AlphaDummy007 R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_039`. -/
@[expose]
noncomputable def nb092AlphaDummy039 (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb092AlphaDummy009 a b))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_040`. -/
@[expose]
noncomputable def nb092AlphaDummy040 (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb092AlphaDummy007 R)))).fv ∪
      ((synCphi (Class.cv (nb092AlphaDummy007 R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_041`. -/
@[expose]
noncomputable def nb092AlphaDummy041 (a : Var) (b : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb092AlphaDummy009 a b)))).fv ∪
      ((synCphi (Class.cv (nb092AlphaDummy009 a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_042`. -/
@[expose]
noncomputable def nb092AlphaDummy042 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy002 R))).fv ∪
      ((Class.cv (nb092AlphaDummy003 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_043`. -/
@[expose]
noncomputable def nb092AlphaDummy043 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy002 R))).fv ∪
      ((Class.cv (nb092AlphaDummy003 R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_044`. -/
@[expose]
noncomputable def nb092AlphaDummy044 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_045`. -/
@[expose]
noncomputable def nb092AlphaDummy045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_046`. -/
@[expose]
noncomputable def nb092AlphaDummy046 (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCphi (Class.cv (nb092AlphaDummy043 R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_047`. -/
@[expose]
noncomputable def nb092AlphaDummy047 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCphi (Class.cv (nb092AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_048`. -/
@[expose]
noncomputable def nb092AlphaDummy048 (R : Class) : Var :=
  (freshVar (((Class.cab (nb092AlphaDummy042 R)
          (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
            (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
              (synCphi (Class.cv (nb092AlphaDummy043 R))))))).fv ∪
      ((Class.cab (nb092AlphaDummy042 R)
          (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
            (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
              (synCphi (Class.cv (nb092AlphaDummy043 R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_049`. -/
@[expose]
noncomputable def nb092AlphaDummy049 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb092AlphaDummy044 x y)
          (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
              (synCphi (Class.cv (nb092AlphaDummy045 x y))))))).fv ∪
      ((Class.cab (nb092AlphaDummy044 x y) (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
              (synCphi (Class.cv (nb092AlphaDummy045 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_050`. -/
@[expose]
noncomputable def nb092AlphaDummy050 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy043 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_051`. -/
@[expose]
noncomputable def nb092AlphaDummy051 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy043 R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_052`. -/
@[expose]
noncomputable def nb092AlphaDummy052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy045 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_053`. -/
@[expose]
noncomputable def nb092AlphaDummy053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy045 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_054`. -/
@[expose]
noncomputable def nb092AlphaDummy054 (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb092AlphaDummy050 R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb092AlphaDummy050 R)) (synC1c))).fv ∪
      ((Class.cv (nb092AlphaDummy050 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_055`. -/
@[expose]
noncomputable def nb092AlphaDummy055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb092AlphaDummy052 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb092AlphaDummy052 x y)) (synC1c))).fv ∪
      ((Class.cv (nb092AlphaDummy052 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_056`. -/
@[expose]
noncomputable def nb092AlphaDummy056 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_057`. -/
@[expose]
noncomputable def nb092AlphaDummy057 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_058`. -/
@[expose]
noncomputable def nb092AlphaDummy058 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_059`. -/
@[expose]
noncomputable def nb092AlphaDummy059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_060`. -/
@[expose]
noncomputable def nb092AlphaDummy060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_061`. -/
@[expose]
noncomputable def nb092AlphaDummy061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_062`. -/
@[expose]
noncomputable def nb092AlphaDummy062 (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb092AlphaDummy057 R))
          (Class.cv (nb092AlphaDummy058 R)))).fv ∪
      ((synCnin (Class.cv (nb092AlphaDummy057 R)) (Class.cv (nb092AlphaDummy058 R)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_063`. -/
@[expose]
noncomputable def nb092AlphaDummy063 (x : Var) (y : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb092AlphaDummy060 x y))
          (Class.cv (nb092AlphaDummy061 x y)))).fv ∪
      ((synCnin (Class.cv (nb092AlphaDummy060 x y))
          (Class.cv (nb092AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_064`. -/
@[expose]
noncomputable def nb092AlphaDummy064 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy057 R))).fv ∪
      ((Class.cv (nb092AlphaDummy058 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_065`. -/
@[expose]
noncomputable def nb092AlphaDummy065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb092AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_066`. -/
@[expose]
noncomputable def nb092AlphaDummy066 (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb092AlphaDummy057 R)))).fv ∪
      ((synCcompl (Class.cv (nb092AlphaDummy058 R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_067`. -/
@[expose]
noncomputable def nb092AlphaDummy067 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb092AlphaDummy060 x y)))).fv ∪
      ((synCcompl (Class.cv (nb092AlphaDummy061 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_068`. -/
@[expose]
noncomputable def nb092AlphaDummy068 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy057 R))).fv ∪
      ((Class.cv (nb092AlphaDummy057 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_069`. -/
@[expose]
noncomputable def nb092AlphaDummy069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
      ((Class.cv (nb092AlphaDummy060 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_070`. -/
@[expose]
noncomputable def nb092AlphaDummy070 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy058 R))).fv ∪
      ((Class.cv (nb092AlphaDummy058 R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_071`. -/
@[expose]
noncomputable def nb092AlphaDummy071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092AlphaDummy061 x y))).fv ∪
      ((Class.cv (nb092AlphaDummy061 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_072`. -/
@[expose]
noncomputable def nb092AlphaDummy072 (R : Class) : Var :=
  (freshVar (((Class.cab (nb092AlphaDummy042 R)
          (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
            (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
              (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy042 R)
          (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
            (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
              (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_073`. -/
@[expose]
noncomputable def nb092AlphaDummy073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb092AlphaDummy044 x y)
          (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
              (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy044 x y)
          (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
              (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_074`. -/
@[expose]
noncomputable def nb092AlphaDummy074 (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb092AlphaDummy043 R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_075`. -/
@[expose]
noncomputable def nb092AlphaDummy075 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb092AlphaDummy045 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_076`. -/
@[expose]
noncomputable def nb092AlphaDummy076 (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb092AlphaDummy043 R)))).fv ∪
      ((synCphi (Class.cv (nb092AlphaDummy043 R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb092_alpha_dummy_077`. -/
@[expose]
noncomputable def nb092AlphaDummy077 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb092AlphaDummy045 x y)))).fv ∪
      ((synCphi (Class.cv (nb092AlphaDummy045 x y)))).fv) 0)

theorem nb092_fresh_000 (R : Class) :
    (nb092AlphaDummy012 R) ∉
      (((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCphi (Class.cv (nb092AlphaDummy007 R))))))).fv ∪
        ((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCphi (Class.cv (nb092AlphaDummy007 R))))))).fv) :=
  by
  simpa only [nb092AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCphi (Class.cv (nb092AlphaDummy007 R))))))).fv ∪
        ((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCphi (Class.cv (nb092AlphaDummy007 R))))))).fv)
      0

theorem nb092_fresh_001 (R : Class) :
    (nb092AlphaDummy036 R) ∉
      (((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb092AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb092_fresh_002 (a : Var) (b : Var) :
    (nb092AlphaDummy013 a b) ∉
      (((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCphi (Class.cv (nb092AlphaDummy009 a b))))))).fv ∪
        ((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCphi (Class.cv (nb092AlphaDummy009 a b))))))).fv) :=
  by
  simpa only [nb092AlphaDummy013] using
    freshVar_not_mem
      (((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCphi (Class.cv (nb092AlphaDummy009 a b))))))).fv ∪
        ((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCphi (Class.cv (nb092AlphaDummy009 a b))))))).fv)
      0

theorem nb092_fresh_003 (a : Var) (b : Var) :
    (nb092AlphaDummy037 a b) ∉
      (((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb092AlphaDummy037] using
    freshVar_not_mem
      (((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb092_fresh_004 (R : Class) :
    (nb092AlphaDummy048 R) ∉
      (((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCphi (Class.cv (nb092AlphaDummy043 R))))))).fv ∪
        ((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCphi (Class.cv (nb092AlphaDummy043 R))))))).fv) :=
  by
  simpa only [nb092AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCphi (Class.cv (nb092AlphaDummy043 R))))))).fv ∪
        ((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCphi (Class.cv (nb092AlphaDummy043 R))))))).fv)
      0

theorem nb092_fresh_005 (R : Class) :
    (nb092AlphaDummy072 R) ∉
      (((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb092AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb092_fresh_006 (x : Var) (y : Var) :
    (nb092AlphaDummy049 x y) ∉
      (((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCphi (Class.cv (nb092AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCphi (Class.cv (nb092AlphaDummy045 x y))))))).fv) :=
  by
  simpa only [nb092AlphaDummy049] using
    freshVar_not_mem
      (((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCphi (Class.cv (nb092AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCphi (Class.cv (nb092AlphaDummy045 x y))))))).fv)
      0

theorem nb092_fresh_007 (x : Var) (y : Var) :
    (nb092AlphaDummy073 x y) ∉
      (((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb092AlphaDummy073] using
    freshVar_not_mem
      (((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb092_fresh_008 (a : Var) (b : Var) :
    (nb092AlphaDummy008 a b) ∉ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) := by
  simpa only [nb092AlphaDummy008] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 0

theorem nb092_fresh_009 (a : Var) (b : Var) :
    (nb092AlphaDummy009 a b) ∉ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) := by
  simpa only [nb092AlphaDummy009] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 1

theorem nb092_distinct_010 (a : Var) (b : Var) :
    (nb092AlphaDummy008 a b) ≠ (nb092AlphaDummy009 a b) := by
  simpa only [nb092AlphaDummy008, nb092AlphaDummy009] using
    (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (i := 0) (j := 1) (by decide))

theorem nb092_fresh_011 (R : Class) :
    (nb092AlphaDummy006 R) ∉
      (((Class.cv (nb092AlphaDummy000 R))).fv ∪ ((Class.cv (nb092AlphaDummy001 R))).fv) :=
  by
  simpa only [nb092AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy000 R))).fv ∪ ((Class.cv (nb092AlphaDummy001 R))).fv)
      0

theorem nb092_fresh_012 (R : Class) :
    (nb092AlphaDummy007 R) ∉
      (((Class.cv (nb092AlphaDummy000 R))).fv ∪ ((Class.cv (nb092AlphaDummy001 R))).fv) :=
  by
  simpa only [nb092AlphaDummy007] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy000 R))).fv ∪ ((Class.cv (nb092AlphaDummy001 R))).fv)
      1

theorem nb092_distinct_013 (R : Class) :
    (nb092AlphaDummy006 R) ≠ (nb092AlphaDummy007 R) := by
  simpa only [nb092AlphaDummy006, nb092AlphaDummy007] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy000 R))).fv ∪
        ((Class.cv (nb092AlphaDummy001 R))).fv) (i := 0) (j := 1) (by decide))

theorem nb092_fresh_014 (R : Class) :
    (nb092AlphaDummy042 R) ∉
      (((Class.cv (nb092AlphaDummy002 R))).fv ∪ ((Class.cv (nb092AlphaDummy003 R))).fv) :=
  by
  simpa only [nb092AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy002 R))).fv ∪ ((Class.cv (nb092AlphaDummy003 R))).fv)
      0

theorem nb092_fresh_015 (R : Class) :
    (nb092AlphaDummy043 R) ∉
      (((Class.cv (nb092AlphaDummy002 R))).fv ∪ ((Class.cv (nb092AlphaDummy003 R))).fv) :=
  by
  simpa only [nb092AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy002 R))).fv ∪ ((Class.cv (nb092AlphaDummy003 R))).fv)
      1

theorem nb092_distinct_016 (R : Class) :
    (nb092AlphaDummy042 R) ≠ (nb092AlphaDummy043 R) := by
  simpa only [nb092AlphaDummy042, nb092AlphaDummy043] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy002 R))).fv ∪
        ((Class.cv (nb092AlphaDummy003 R))).fv) (i := 0) (j := 1) (by decide))

theorem nb092_fresh_017 (R : Class) :
    (nb092AlphaDummy014 R) ∉ (((Class.cv (nb092AlphaDummy007 R))).fv) := by
  simpa only [nb092AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy007 R))).fv) 0

theorem nb092_fresh_018 (R : Class) :
    (nb092AlphaDummy015 R) ∉ (((Class.cv (nb092AlphaDummy007 R))).fv) := by
  simpa only [nb092AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy007 R))).fv) 1

theorem nb092_distinct_019 (R : Class) :
    (nb092AlphaDummy014 R) ≠ (nb092AlphaDummy015 R) := by
  simpa only [nb092AlphaDummy014, nb092AlphaDummy015] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy007 R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb092_fresh_020 (a : Var) (b : Var) :
    (nb092AlphaDummy016 a b) ∉ (((Class.cv (nb092AlphaDummy009 a b))).fv) := by
  simpa only [nb092AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy009 a b))).fv) 0

theorem nb092_fresh_021 (a : Var) (b : Var) :
    (nb092AlphaDummy017 a b) ∉ (((Class.cv (nb092AlphaDummy009 a b))).fv) := by
  simpa only [nb092AlphaDummy017] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy009 a b))).fv) 1

theorem nb092_distinct_022 (a : Var) (b : Var) :
    (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy017 a b) := by
  simpa only [nb092AlphaDummy016, nb092AlphaDummy017] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy009 a b))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb092_fresh_023 (R : Class) :
    (nb092AlphaDummy020 R) ∉
      (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) 0

theorem nb092_fresh_024 (R : Class) :
    (nb092AlphaDummy021 R) ∉
      (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) 1

theorem nb092_fresh_025 (R : Class) :
    (nb092AlphaDummy022 R) ∉
      (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) 2

theorem nb092_distinct_026 (R : Class) :
    (nb092AlphaDummy020 R) ≠ (nb092AlphaDummy021 R) := by
  simpa only [nb092AlphaDummy020, nb092AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb092_distinct_027 (R : Class) :
    (nb092AlphaDummy020 R) ≠ (nb092AlphaDummy022 R) := by
  simpa only [nb092AlphaDummy020, nb092AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb092_distinct_028 (R : Class) :
    (nb092AlphaDummy021 R) ≠ (nb092AlphaDummy022 R) := by
  simpa only [nb092AlphaDummy021, nb092AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb092_fresh_029 (a : Var) (b : Var) :
    (nb092AlphaDummy023 a b) ∉
      (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 0

theorem nb092_fresh_030 (a : Var) (b : Var) :
    (nb092AlphaDummy024 a b) ∉
      (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 1

theorem nb092_fresh_031 (a : Var) (b : Var) :
    (nb092AlphaDummy025 a b) ∉
      (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) 2

theorem nb092_distinct_032 (a : Var) (b : Var) :
    (nb092AlphaDummy023 a b) ≠ (nb092AlphaDummy024 a b) := by
  simpa only [nb092AlphaDummy023, nb092AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb092_distinct_033 (a : Var) (b : Var) :
    (nb092AlphaDummy023 a b) ≠ (nb092AlphaDummy025 a b) := by
  simpa only [nb092AlphaDummy023, nb092AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb092_distinct_034 (a : Var) (b : Var) :
    (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy025 a b) := by
  simpa only [nb092AlphaDummy024, nb092AlphaDummy025] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb092_fresh_035 (R : Class) :
    (nb092AlphaDummy032 R) ∉
      (((Class.cv (nb092AlphaDummy021 R))).fv ∪ ((Class.cv (nb092AlphaDummy021 R))).fv) :=
  by
  simpa only [nb092AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy021 R))).fv ∪ ((Class.cv (nb092AlphaDummy021 R))).fv)
      0

theorem nb092_fresh_036 (R : Class) :
    (nb092AlphaDummy028 R) ∉
      (((Class.cv (nb092AlphaDummy021 R))).fv ∪ ((Class.cv (nb092AlphaDummy022 R))).fv) :=
  by
  simpa only [nb092AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy021 R))).fv ∪ ((Class.cv (nb092AlphaDummy022 R))).fv)
      0

theorem nb092_fresh_037 (R : Class) :
    (nb092AlphaDummy034 R) ∉
      (((Class.cv (nb092AlphaDummy022 R))).fv ∪ ((Class.cv (nb092AlphaDummy022 R))).fv) :=
  by
  simpa only [nb092AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy022 R))).fv ∪ ((Class.cv (nb092AlphaDummy022 R))).fv)
      0

theorem nb092_fresh_038 (a : Var) (b : Var) :
    (nb092AlphaDummy033 a b) ∉
      (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy024 a b))).fv) :=
  by
  simpa only [nb092AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy024 a b))).fv)
      0

theorem nb092_fresh_039 (a : Var) (b : Var) :
    (nb092AlphaDummy029 a b) ∉
      (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy025 a b))).fv) :=
  by
  simpa only [nb092AlphaDummy029] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy025 a b))).fv)
      0

theorem nb092_fresh_040 (a : Var) (b : Var) :
    (nb092AlphaDummy035 a b) ∉
      (((Class.cv (nb092AlphaDummy025 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy025 a b))).fv) :=
  by
  simpa only [nb092AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy025 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy025 a b))).fv)
      0

theorem nb092_fresh_041 (R : Class) :
    (nb092AlphaDummy050 R) ∉ (((Class.cv (nb092AlphaDummy043 R))).fv) := by
  simpa only [nb092AlphaDummy050] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy043 R))).fv) 0

theorem nb092_fresh_042 (R : Class) :
    (nb092AlphaDummy051 R) ∉ (((Class.cv (nb092AlphaDummy043 R))).fv) := by
  simpa only [nb092AlphaDummy051] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy043 R))).fv) 1

theorem nb092_distinct_043 (R : Class) :
    (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy051 R) := by
  simpa only [nb092AlphaDummy050, nb092AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy043 R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb092_fresh_044 (x : Var) (y : Var) :
    (nb092AlphaDummy052 x y) ∉ (((Class.cv (nb092AlphaDummy045 x y))).fv) := by
  simpa only [nb092AlphaDummy052] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy045 x y))).fv) 0

theorem nb092_fresh_045 (x : Var) (y : Var) :
    (nb092AlphaDummy053 x y) ∉ (((Class.cv (nb092AlphaDummy045 x y))).fv) := by
  simpa only [nb092AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy045 x y))).fv) 1

theorem nb092_distinct_046 (x : Var) (y : Var) :
    (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy053 x y) := by
  simpa only [nb092AlphaDummy052, nb092AlphaDummy053] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy045 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb092_fresh_047 (R : Class) :
    (nb092AlphaDummy056 R) ∉
      (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) 0

theorem nb092_fresh_048 (R : Class) :
    (nb092AlphaDummy057 R) ∉
      (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy057] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) 1

theorem nb092_fresh_049 (R : Class) :
    (nb092AlphaDummy058 R) ∉
      (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy058] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) 2

theorem nb092_distinct_050 (R : Class) :
    (nb092AlphaDummy056 R) ≠ (nb092AlphaDummy057 R) := by
  simpa only [nb092AlphaDummy056, nb092AlphaDummy057] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb092_distinct_051 (R : Class) :
    (nb092AlphaDummy056 R) ≠ (nb092AlphaDummy058 R) := by
  simpa only [nb092AlphaDummy056, nb092AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb092_distinct_052 (R : Class) :
    (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy058 R) := by
  simpa only [nb092AlphaDummy057, nb092AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb092_fresh_053 (x : Var) (y : Var) :
    (nb092AlphaDummy059 x y) ∉
      (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 0

theorem nb092_fresh_054 (x : Var) (y : Var) :
    (nb092AlphaDummy060 x y) ∉
      (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 1

theorem nb092_fresh_055 (x : Var) (y : Var) :
    (nb092AlphaDummy061 x y) ∉
      (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb092AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) 2

theorem nb092_distinct_056 (x : Var) (y : Var) :
    (nb092AlphaDummy059 x y) ≠ (nb092AlphaDummy060 x y) := by
  simpa only [nb092AlphaDummy059, nb092AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb092_distinct_057 (x : Var) (y : Var) :
    (nb092AlphaDummy059 x y) ≠ (nb092AlphaDummy061 x y) := by
  simpa only [nb092AlphaDummy059, nb092AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb092_distinct_058 (x : Var) (y : Var) :
    (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy061 x y) := by
  simpa only [nb092AlphaDummy060, nb092AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb092_fresh_059 (R : Class) :
    (nb092AlphaDummy068 R) ∉
      (((Class.cv (nb092AlphaDummy057 R))).fv ∪ ((Class.cv (nb092AlphaDummy057 R))).fv) :=
  by
  simpa only [nb092AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy057 R))).fv ∪ ((Class.cv (nb092AlphaDummy057 R))).fv)
      0

theorem nb092_fresh_060 (R : Class) :
    (nb092AlphaDummy064 R) ∉
      (((Class.cv (nb092AlphaDummy057 R))).fv ∪ ((Class.cv (nb092AlphaDummy058 R))).fv) :=
  by
  simpa only [nb092AlphaDummy064] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy057 R))).fv ∪ ((Class.cv (nb092AlphaDummy058 R))).fv)
      0

theorem nb092_fresh_061 (R : Class) :
    (nb092AlphaDummy070 R) ∉
      (((Class.cv (nb092AlphaDummy058 R))).fv ∪ ((Class.cv (nb092AlphaDummy058 R))).fv) :=
  by
  simpa only [nb092AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy058 R))).fv ∪ ((Class.cv (nb092AlphaDummy058 R))).fv)
      0

theorem nb092_fresh_062 (x : Var) (y : Var) :
    (nb092AlphaDummy069 x y) ∉
      (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy060 x y))).fv) :=
  by
  simpa only [nb092AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy060 x y))).fv)
      0

theorem nb092_fresh_063 (x : Var) (y : Var) :
    (nb092AlphaDummy065 x y) ∉
      (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb092AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy061 x y))).fv)
      0

theorem nb092_fresh_064 (x : Var) (y : Var) :
    (nb092AlphaDummy071 x y) ∉
      (((Class.cv (nb092AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy061 x y))).fv) :=
  by
  simpa only [nb092AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb092AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy061 x y))).fv)
      0

theorem nb092_fresh_065 (x : Var) (y : Var) :
    (nb092AlphaDummy044 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb092AlphaDummy044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb092_fresh_066 (x : Var) (y : Var) :
    (nb092AlphaDummy045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb092AlphaDummy045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb092_distinct_067 (x : Var) (y : Var) :
    (nb092AlphaDummy044 x y) ≠ (nb092AlphaDummy045 x y) := by
  simpa only [nb092AlphaDummy044, nb092AlphaDummy045] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb092_fresh_068 (R : Class) :
    (nb092AlphaDummy018 R) ∉
      (((Wff.classMem (Class.cv (nb092AlphaDummy014 R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy014 R)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy014 R))).fv) :=
  by
  simpa only [nb092AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb092AlphaDummy014 R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy014 R)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy014 R))).fv)
      0

theorem nb092_fresh_069 (a : Var) (b : Var) :
    (nb092AlphaDummy019 a b) ∉
      (((Wff.classMem (Class.cv (nb092AlphaDummy016 a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy016 a b)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy016 a b))).fv) :=
  by
  simpa only [nb092AlphaDummy019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb092AlphaDummy016 a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy016 a b)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy016 a b))).fv)
      0

theorem nb092_fresh_070 (R : Class) :
    (nb092AlphaDummy054 R) ∉
      (((Wff.classMem (Class.cv (nb092AlphaDummy050 R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy050 R)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy050 R))).fv) :=
  by
  simpa only [nb092AlphaDummy054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb092AlphaDummy050 R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy050 R)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy050 R))).fv)
      0

theorem nb092_fresh_071 (x : Var) (y : Var) :
    (nb092AlphaDummy055 x y) ∉
      (((Wff.classMem (Class.cv (nb092AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy052 x y))).fv) :=
  by
  simpa only [nb092AlphaDummy055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb092AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy052 x y))).fv)
      0

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

theorem nb092_fresh_072 (R : Class) :
    (nb092AlphaDummy010 R) ∉
      (((synCcompl (Class.cab (nb092AlphaDummy006 R)
              (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                  (synCphi (Class.cv (nb092AlphaDummy007 R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy006 R)
              (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb092AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb092AlphaDummy006 R)
              (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                  (synCphi (Class.cv (nb092AlphaDummy007 R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy006 R)
              (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb092_fresh_073 (a : Var) (b : Var) :
    (nb092AlphaDummy011 a b) ∉
      (((synCcompl (Class.cab (nb092AlphaDummy008 a b)
              (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                  (synCphi (Class.cv (nb092AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy008 a b)
              (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb092AlphaDummy011] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb092AlphaDummy008 a b)
              (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                  (synCphi (Class.cv (nb092AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy008 a b)
              (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb092_fresh_074 (R : Class) :
    (nb092AlphaDummy046 R) ∉
      (((synCcompl (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCphi (Class.cv (nb092AlphaDummy043 R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb092AlphaDummy046] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCphi (Class.cv (nb092AlphaDummy043 R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb092_fresh_075 (x : Var) (y : Var) :
    (nb092AlphaDummy047 x y) ∉
      (((synCcompl (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCphi (Class.cv (nb092AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb092AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCphi (Class.cv (nb092AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb092_fresh_076 (R : Class) :
    (nb092AlphaDummy030 R) ∉
      (((synCcompl (Class.cv (nb092AlphaDummy021 R)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy022 R)))).fv) :=
  by
  simpa only [nb092AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb092AlphaDummy021 R)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy022 R)))).fv)
      0

theorem nb092_fresh_077 (a : Var) (b : Var) :
    (nb092AlphaDummy031 a b) ∉
      (((synCcompl (Class.cv (nb092AlphaDummy024 a b)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy025 a b)))).fv) :=
  by
  simpa only [nb092AlphaDummy031] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb092AlphaDummy024 a b)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy025 a b)))).fv)
      0

theorem nb092_fresh_078 (R : Class) :
    (nb092AlphaDummy066 R) ∉
      (((synCcompl (Class.cv (nb092AlphaDummy057 R)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy058 R)))).fv) :=
  by
  simpa only [nb092AlphaDummy066] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb092AlphaDummy057 R)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy058 R)))).fv)
      0

theorem nb092_fresh_079 (x : Var) (y : Var) :
    (nb092AlphaDummy067 x y) ∉
      (((synCcompl (Class.cv (nb092AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb092AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb092AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy061 x y)))).fv)
      0

theorem nb092_fresh_080 (R : Class) :
    (nb092AlphaDummy038 R) ∉
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy007 R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb092AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy007 R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb092_fresh_081 (a : Var) (b : Var) :
    (nb092AlphaDummy039 a b) ∉
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy009 a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb092AlphaDummy039] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy009 a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb092_fresh_082 (R : Class) :
    (nb092AlphaDummy074 R) ∉
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy043 R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb092AlphaDummy074] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy043 R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb092_fresh_083 (x : Var) (y : Var) :
    (nb092AlphaDummy075 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb092AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb092_fresh_084 (R : Class) :
    (nb092AlphaDummy026 R) ∉
      (((synCnin (Class.cv (nb092AlphaDummy021 R))
            (Class.cv (nb092AlphaDummy022 R)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy021 R))
            (Class.cv (nb092AlphaDummy022 R)))).fv) :=
  by
  simpa only [nb092AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb092AlphaDummy021 R))
            (Class.cv (nb092AlphaDummy022 R)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy021 R))
            (Class.cv (nb092AlphaDummy022 R)))).fv)
      0

theorem nb092_fresh_085 (a : Var) (b : Var) :
    (nb092AlphaDummy027 a b) ∉
      (((synCnin (Class.cv (nb092AlphaDummy024 a b))
            (Class.cv (nb092AlphaDummy025 a b)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy024 a b))
            (Class.cv (nb092AlphaDummy025 a b)))).fv) :=
  by
  simpa only [nb092AlphaDummy027] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb092AlphaDummy024 a b))
            (Class.cv (nb092AlphaDummy025 a b)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy024 a b))
            (Class.cv (nb092AlphaDummy025 a b)))).fv)
      0

theorem nb092_fresh_086 (R : Class) :
    (nb092AlphaDummy062 R) ∉
      (((synCnin (Class.cv (nb092AlphaDummy057 R))
            (Class.cv (nb092AlphaDummy058 R)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy057 R))
            (Class.cv (nb092AlphaDummy058 R)))).fv) :=
  by
  simpa only [nb092AlphaDummy062] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb092AlphaDummy057 R))
            (Class.cv (nb092AlphaDummy058 R)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy057 R))
            (Class.cv (nb092AlphaDummy058 R)))).fv)
      0

theorem nb092_fresh_087 (x : Var) (y : Var) :
    (nb092AlphaDummy063 x y) ∉
      (((synCnin (Class.cv (nb092AlphaDummy060 x y))
            (Class.cv (nb092AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy060 x y))
            (Class.cv (nb092AlphaDummy061 x y)))).fv) :=
  by
  simpa only [nb092AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb092AlphaDummy060 x y))
            (Class.cv (nb092AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy060 x y))
            (Class.cv (nb092AlphaDummy061 x y)))).fv)
      0

theorem nb092_fresh_088 (R : Class) :
    (nb092AlphaDummy040 R) ∉
      (((synCphi (Class.cv (nb092AlphaDummy007 R)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy007 R)))).fv) :=
  by
  simpa only [nb092AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb092AlphaDummy007 R)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy007 R)))).fv)
      0

theorem nb092_fresh_089 (a : Var) (b : Var) :
    (nb092AlphaDummy041 a b) ∉
      (((synCphi (Class.cv (nb092AlphaDummy009 a b)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy009 a b)))).fv) :=
  by
  simpa only [nb092AlphaDummy041] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb092AlphaDummy009 a b)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy009 a b)))).fv)
      0

theorem nb092_fresh_090 (R : Class) :
    (nb092AlphaDummy076 R) ∉
      (((synCphi (Class.cv (nb092AlphaDummy043 R)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy043 R)))).fv) :=
  by
  simpa only [nb092AlphaDummy076] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb092AlphaDummy043 R)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy043 R)))).fv)
      0

theorem nb092_fresh_091 (x : Var) (y : Var) :
    (nb092AlphaDummy077 x y) ∉
      (((synCphi (Class.cv (nb092AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy045 x y)))).fv) :=
  by
  simpa only [nb092AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb092AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy045 x y)))).fv)
      0

theorem nb092_fresh_092 (R : Class) : (nb092AlphaDummy000 R) ∉ ((R).fv) := by
  simpa only [nb092AlphaDummy000] using freshVar_not_mem ((R).fv) 0

theorem nb092_fresh_093 (R : Class) : (nb092AlphaDummy001 R) ∉ ((R).fv) := by
  simpa only [nb092AlphaDummy001] using freshVar_not_mem ((R).fv) 1

theorem nb092_fresh_094 (R : Class) : (nb092AlphaDummy002 R) ∉ ((R).fv) := by
  simpa only [nb092AlphaDummy002] using freshVar_not_mem ((R).fv) 2

theorem nb092_fresh_095 (R : Class) : (nb092AlphaDummy003 R) ∉ ((R).fv) := by
  simpa only [nb092AlphaDummy003] using freshVar_not_mem ((R).fv) 3

theorem nb092_distinct_096 (R : Class) :
    (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy001 R) := by
  simpa only [nb092AlphaDummy000, nb092AlphaDummy001] using
    (freshVar_injective ((R).fv) (i := 0) (j := 1) (by decide))

theorem nb092_distinct_097 (R : Class) :
    (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy002 R) := by
  simpa only [nb092AlphaDummy000, nb092AlphaDummy002] using
    (freshVar_injective ((R).fv) (i := 0) (j := 2) (by decide))

theorem nb092_distinct_098 (R : Class) :
    (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy003 R) := by
  simpa only [nb092AlphaDummy000, nb092AlphaDummy003] using
    (freshVar_injective ((R).fv) (i := 0) (j := 3) (by decide))

theorem nb092_distinct_099 (R : Class) :
    (nb092AlphaDummy001 R) ≠ (nb092AlphaDummy002 R) := by
  simpa only [nb092AlphaDummy001, nb092AlphaDummy002] using
    (freshVar_injective ((R).fv) (i := 1) (j := 2) (by decide))

theorem nb092_distinct_100 (R : Class) :
    (nb092AlphaDummy001 R) ≠ (nb092AlphaDummy003 R) := by
  simpa only [nb092AlphaDummy001, nb092AlphaDummy003] using
    (freshVar_injective ((R).fv) (i := 1) (j := 3) (by decide))

theorem nb092_distinct_101 (R : Class) :
    (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy003 R) := by
  simpa only [nb092AlphaDummy002, nb092AlphaDummy003] using
    (freshVar_injective ((R).fv) (i := 2) (j := 3) (by decide))

theorem nb092_fresh_102 (R : Class) :
    (nb092AlphaDummy004 R) ∉
      (({(nb092AlphaDummy000 R)} : Finset Var) ∪ ({(nb092AlphaDummy001 R)} : Finset Var) ∪
        ((synWrex (nb092AlphaDummy002 R) (Class.cv (nb092AlphaDummy000 R))
            (synWrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
              (synWbr (Class.cv (nb092AlphaDummy002 R)) R
                (Class.cv (nb092AlphaDummy003 R)))))).fv) :=
  by
  simpa only [nb092AlphaDummy004] using
    freshVar_not_mem
      (({(nb092AlphaDummy000 R)} : Finset Var) ∪ ({(nb092AlphaDummy001 R)} : Finset Var) ∪
        ((synWrex (nb092AlphaDummy002 R) (Class.cv (nb092AlphaDummy000 R))
            (synWrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
              (synWbr (Class.cv (nb092AlphaDummy002 R)) R
                (Class.cv (nb092AlphaDummy003 R)))))).fv)
      0

theorem nb092_fresh_103 (x : Var) (y : Var) (R : Class) (a : Var) (b : Var) :
    (nb092AlphaDummy005 x y R a b) ∉
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y))))).fv) :=
  by
  simpa only [nb092AlphaDummy005] using
    freshVar_not_mem
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y))))).fv)
      0

theorem nb092_support_mem_0000 (R : Class) :
    (nb092AlphaDummy000 R) ∈
      (({(nb092AlphaDummy000 R)} : Finset Var) ∪ ({(nb092AlphaDummy001 R)} : Finset Var) ∪
        ((synWrex (nb092AlphaDummy002 R) (Class.cv (nb092AlphaDummy000 R))
            (synWrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
              (synWbr (Class.cv (nb092AlphaDummy002 R)) R
                (Class.cv (nb092AlphaDummy003 R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0001 (x : Var) (y : Var) (R : Class) (a : Var) (b : Var) :
    a ∈
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0002 (R : Class) :
    (nb092AlphaDummy001 R) ∈
      (({(nb092AlphaDummy000 R)} : Finset Var) ∪ ({(nb092AlphaDummy001 R)} : Finset Var) ∪
        ((synWrex (nb092AlphaDummy002 R) (Class.cv (nb092AlphaDummy000 R))
            (synWrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
              (synWbr (Class.cv (nb092AlphaDummy002 R)) R
                (Class.cv (nb092AlphaDummy003 R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0003 (x : Var) (y : Var) (R : Class) (a : Var) (b : Var) :
    b ∈
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0004 (R : Class) :
    (nb092AlphaDummy000 R) ∈
      (((Class.cv (nb092AlphaDummy000 R))).fv ∪ ((Class.cv (nb092AlphaDummy001 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0005 (R : Class) :
    (nb092AlphaDummy000 R) ∈
      (((synCcompl (Class.cab (nb092AlphaDummy006 R)
              (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                  (synCphi (Class.cv (nb092AlphaDummy007 R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy006 R)
              (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy006 R) from (by
          unfold nb092AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0004 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy007 R) from (by
            unfold nb092AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0004 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0006 (a : Var) (b : Var) :
    a ∈ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0007 (a : Var) (b : Var) :
    a ∈
      (((synCcompl (Class.cab (nb092AlphaDummy008 a b)
              (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                  (synCphi (Class.cv (nb092AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy008 a b)
              (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb092AlphaDummy008 a b) from (by
          unfold nb092AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0006 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb092AlphaDummy009 a b) from (by
            unfold nb092AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0006 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0008 (R : Class) :
    (nb092AlphaDummy000 R) ∈
      (((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCphi (Class.cv (nb092AlphaDummy007 R))))))).fv ∪
        ((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCphi (Class.cv (nb092AlphaDummy007 R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy006 R) from (by
          unfold nb092AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0004 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy007 R) from (by
            unfold nb092AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0004 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0009 (a : Var) (b : Var) :
    a ∈
      (((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCphi (Class.cv (nb092AlphaDummy009 a b))))))).fv ∪
        ((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCphi (Class.cv (nb092AlphaDummy009 a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb092AlphaDummy008 a b) from (by
          unfold nb092AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0006 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb092AlphaDummy009 a b) from (by
            unfold nb092AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0006 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0010 (R : Class) :
    (nb092AlphaDummy007 R) ∈ (((Class.cv (nb092AlphaDummy007 R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0011 (a : Var) (b : Var) :
    (nb092AlphaDummy009 a b) ∈ (((Class.cv (nb092AlphaDummy009 a b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0012 (R : Class) :
    (nb092AlphaDummy014 R) ∈
      (((Wff.classMem (Class.cv (nb092AlphaDummy014 R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy014 R)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy014 R))).fv) :=
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

theorem nb092_support_mem_0013 (a : Var) (b : Var) :
    (nb092AlphaDummy016 a b) ∈
      (((Wff.classMem (Class.cv (nb092AlphaDummy016 a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy016 a b)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy016 a b))).fv) :=
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

theorem nb092_support_mem_0014 (R : Class) :
    (nb092AlphaDummy014 R) ∈
      (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0015 (a : Var) (b : Var) :
    (nb092AlphaDummy016 a b) ∈
      (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0016 (R : Class) :
    (nb092AlphaDummy021 R) ∈
      (((synCnin (Class.cv (nb092AlphaDummy021 R))
            (Class.cv (nb092AlphaDummy022 R)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy021 R))
            (Class.cv (nb092AlphaDummy022 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0017 (a : Var) (b : Var) :
    (nb092AlphaDummy024 a b) ∈
      (((synCnin (Class.cv (nb092AlphaDummy024 a b))
            (Class.cv (nb092AlphaDummy025 a b)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy024 a b))
            (Class.cv (nb092AlphaDummy025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0018 (R : Class) :
    (nb092AlphaDummy021 R) ∈
      (((Class.cv (nb092AlphaDummy021 R))).fv ∪ ((Class.cv (nb092AlphaDummy022 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0019 (a : Var) (b : Var) :
    (nb092AlphaDummy024 a b) ∈
      (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0020 (R : Class) :
    (nb092AlphaDummy022 R) ∈
      (((synCnin (Class.cv (nb092AlphaDummy021 R))
            (Class.cv (nb092AlphaDummy022 R)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy021 R))
            (Class.cv (nb092AlphaDummy022 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0021 (a : Var) (b : Var) :
    (nb092AlphaDummy025 a b) ∈
      (((synCnin (Class.cv (nb092AlphaDummy024 a b))
            (Class.cv (nb092AlphaDummy025 a b)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy024 a b))
            (Class.cv (nb092AlphaDummy025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0022 (R : Class) :
    (nb092AlphaDummy022 R) ∈
      (((Class.cv (nb092AlphaDummy021 R))).fv ∪ ((Class.cv (nb092AlphaDummy022 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0023 (a : Var) (b : Var) :
    (nb092AlphaDummy025 a b) ∈
      (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0024 (R : Class) :
    (nb092AlphaDummy021 R) ∈
      (((synCcompl (Class.cv (nb092AlphaDummy021 R)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy022 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0025 (a : Var) (b : Var) :
    (nb092AlphaDummy024 a b) ∈
      (((synCcompl (Class.cv (nb092AlphaDummy024 a b)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0026 (R : Class) :
    (nb092AlphaDummy021 R) ∈
      (((Class.cv (nb092AlphaDummy021 R))).fv ∪ ((Class.cv (nb092AlphaDummy021 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0027 (a : Var) (b : Var) :
    (nb092AlphaDummy024 a b) ∈
      (((Class.cv (nb092AlphaDummy024 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy024 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0028 (R : Class) :
    (nb092AlphaDummy022 R) ∈
      (((synCcompl (Class.cv (nb092AlphaDummy021 R)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy022 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0029 (a : Var) (b : Var) :
    (nb092AlphaDummy025 a b) ∈
      (((synCcompl (Class.cv (nb092AlphaDummy024 a b)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0030 (R : Class) :
    (nb092AlphaDummy022 R) ∈
      (((Class.cv (nb092AlphaDummy022 R))).fv ∪ ((Class.cv (nb092AlphaDummy022 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0031 (a : Var) (b : Var) :
    (nb092AlphaDummy025 a b) ∈
      (((Class.cv (nb092AlphaDummy025 a b))).fv ∪
        ((Class.cv (nb092AlphaDummy025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0032 (R : Class) :
    (nb092AlphaDummy001 R) ∈
      (((Class.cv (nb092AlphaDummy000 R))).fv ∪ ((Class.cv (nb092AlphaDummy001 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0033 (R : Class) :
    (nb092AlphaDummy001 R) ∈
      (((synCcompl (Class.cab (nb092AlphaDummy006 R)
              (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy000 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                  (synCphi (Class.cv (nb092AlphaDummy007 R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy006 R)
              (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092AlphaDummy001 R) ≠ (nb092AlphaDummy006 R) from (by
          unfold nb092AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092AlphaDummy001 R) ≠ (nb092AlphaDummy007 R) from (by
            unfold nb092AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0034 (a : Var) (b : Var) :
    b ∈ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0035 (a : Var) (b : Var) :
    b ∈
      (((synCcompl (Class.cab (nb092AlphaDummy008 a b)
              (synWrex (nb092AlphaDummy009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                  (synCphi (Class.cv (nb092AlphaDummy009 a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy008 a b)
              (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb092AlphaDummy008 a b) from (by
          unfold nb092AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0034 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb092AlphaDummy009 a b) from (by
            unfold nb092AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0034 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0036 (R : Class) :
    (nb092AlphaDummy001 R) ∈
      (((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy006 R)
            (synWrex (nb092AlphaDummy007 R) (Class.cv (nb092AlphaDummy001 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy006 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy007 R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092AlphaDummy001 R) ≠ (nb092AlphaDummy006 R) from (by
          unfold nb092AlphaDummy006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092AlphaDummy001 R) ≠ (nb092AlphaDummy007 R) from (by
            unfold nb092AlphaDummy007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0037 (a : Var) (b : Var) :
    b ∈
      (((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy008 a b)
            (synWrex (nb092AlphaDummy009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092AlphaDummy008 a b))
                (synCun (synCphi (Class.cv (nb092AlphaDummy009 a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb092AlphaDummy008 a b) from (by
          unfold nb092AlphaDummy008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0034 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb092AlphaDummy009 a b) from (by
            unfold nb092AlphaDummy009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0034 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0038 (R : Class) :
    (nb092AlphaDummy007 R) ∈
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy007 R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0039 (a : Var) (b : Var) :
    (nb092AlphaDummy009 a b) ∈
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy009 a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0040 (R : Class) :
    (nb092AlphaDummy007 R) ∈
      (((synCphi (Class.cv (nb092AlphaDummy007 R)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy007 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0041 (a : Var) (b : Var) :
    (nb092AlphaDummy009 a b) ∈
      (((synCphi (Class.cv (nb092AlphaDummy009 a b)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy009 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0042 (R : Class) :
    (nb092AlphaDummy002 R) ∈
      (((Class.cv (nb092AlphaDummy002 R))).fv ∪ ((Class.cv (nb092AlphaDummy003 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0043 (R : Class) :
    (nb092AlphaDummy002 R) ∈
      (((synCcompl (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCphi (Class.cv (nb092AlphaDummy043 R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy042 R) from (by
          unfold nb092AlphaDummy042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0042 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy043 R) from (by
            unfold nb092AlphaDummy043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0042 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0044 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0045 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCphi (Class.cv (nb092AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb092AlphaDummy044 x y) from (by
          unfold nb092AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0044 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb092AlphaDummy045 x y) from (by
            unfold nb092AlphaDummy045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0044 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0046 (R : Class) :
    (nb092AlphaDummy002 R) ∈
      (((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCphi (Class.cv (nb092AlphaDummy043 R))))))).fv ∪
        ((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCphi (Class.cv (nb092AlphaDummy043 R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy042 R) from (by
          unfold nb092AlphaDummy042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0042 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy043 R) from (by
            unfold nb092AlphaDummy043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0042 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0047 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCphi (Class.cv (nb092AlphaDummy045 x y))))))).fv ∪
        ((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCphi (Class.cv (nb092AlphaDummy045 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb092AlphaDummy044 x y) from (by
          unfold nb092AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0044 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb092AlphaDummy045 x y) from (by
            unfold nb092AlphaDummy045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0044 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0048 (R : Class) :
    (nb092AlphaDummy043 R) ∈ (((Class.cv (nb092AlphaDummy043 R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0049 (x : Var) (y : Var) :
    (nb092AlphaDummy045 x y) ∈ (((Class.cv (nb092AlphaDummy045 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0050 (R : Class) :
    (nb092AlphaDummy050 R) ∈
      (((Wff.classMem (Class.cv (nb092AlphaDummy050 R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy050 R)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy050 R))).fv) :=
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

theorem nb092_support_mem_0051 (x : Var) (y : Var) :
    (nb092AlphaDummy052 x y) ∈
      (((Wff.classMem (Class.cv (nb092AlphaDummy052 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb092AlphaDummy052 x y)) (synC1c))).fv ∪
        ((Class.cv (nb092AlphaDummy052 x y))).fv) :=
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

theorem nb092_support_mem_0052 (R : Class) :
    (nb092AlphaDummy050 R) ∈
      (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0053 (x : Var) (y : Var) :
    (nb092AlphaDummy052 x y) ∈
      (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0054 (R : Class) :
    (nb092AlphaDummy057 R) ∈
      (((synCnin (Class.cv (nb092AlphaDummy057 R))
            (Class.cv (nb092AlphaDummy058 R)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy057 R))
            (Class.cv (nb092AlphaDummy058 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0055 (x : Var) (y : Var) :
    (nb092AlphaDummy060 x y) ∈
      (((synCnin (Class.cv (nb092AlphaDummy060 x y))
            (Class.cv (nb092AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy060 x y))
            (Class.cv (nb092AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0056 (R : Class) :
    (nb092AlphaDummy057 R) ∈
      (((Class.cv (nb092AlphaDummy057 R))).fv ∪ ((Class.cv (nb092AlphaDummy058 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0057 (x : Var) (y : Var) :
    (nb092AlphaDummy060 x y) ∈
      (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0058 (R : Class) :
    (nb092AlphaDummy058 R) ∈
      (((synCnin (Class.cv (nb092AlphaDummy057 R))
            (Class.cv (nb092AlphaDummy058 R)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy057 R))
            (Class.cv (nb092AlphaDummy058 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0059 (x : Var) (y : Var) :
    (nb092AlphaDummy061 x y) ∈
      (((synCnin (Class.cv (nb092AlphaDummy060 x y))
            (Class.cv (nb092AlphaDummy061 x y)))).fv ∪
        ((synCnin (Class.cv (nb092AlphaDummy060 x y))
            (Class.cv (nb092AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0060 (R : Class) :
    (nb092AlphaDummy058 R) ∈
      (((Class.cv (nb092AlphaDummy057 R))).fv ∪ ((Class.cv (nb092AlphaDummy058 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0061 (x : Var) (y : Var) :
    (nb092AlphaDummy061 x y) ∈
      (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0062 (R : Class) :
    (nb092AlphaDummy057 R) ∈
      (((synCcompl (Class.cv (nb092AlphaDummy057 R)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy058 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0063 (x : Var) (y : Var) :
    (nb092AlphaDummy060 x y) ∈
      (((synCcompl (Class.cv (nb092AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0064 (R : Class) :
    (nb092AlphaDummy057 R) ∈
      (((Class.cv (nb092AlphaDummy057 R))).fv ∪ ((Class.cv (nb092AlphaDummy057 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0065 (x : Var) (y : Var) :
    (nb092AlphaDummy060 x y) ∈
      (((Class.cv (nb092AlphaDummy060 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0066 (R : Class) :
    (nb092AlphaDummy058 R) ∈
      (((synCcompl (Class.cv (nb092AlphaDummy057 R)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy058 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0067 (x : Var) (y : Var) :
    (nb092AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb092AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb092AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0068 (R : Class) :
    (nb092AlphaDummy058 R) ∈
      (((Class.cv (nb092AlphaDummy058 R))).fv ∪ ((Class.cv (nb092AlphaDummy058 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0069 (x : Var) (y : Var) :
    (nb092AlphaDummy061 x y) ∈
      (((Class.cv (nb092AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb092AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0070 (R : Class) :
    (nb092AlphaDummy003 R) ∈
      (((Class.cv (nb092AlphaDummy002 R))).fv ∪ ((Class.cv (nb092AlphaDummy003 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0071 (R : Class) :
    (nb092AlphaDummy003 R) ∈
      (((synCcompl (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCphi (Class.cv (nb092AlphaDummy043 R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092AlphaDummy003 R) ≠ (nb092AlphaDummy042 R) from (by
          unfold nb092AlphaDummy042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092AlphaDummy003 R) ≠ (nb092AlphaDummy043 R) from (by
            unfold nb092AlphaDummy043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0072 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0073 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCphi (Class.cv (nb092AlphaDummy045 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb092AlphaDummy044 x y) from (by
          unfold nb092AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb092AlphaDummy045 x y) from (by
            unfold nb092AlphaDummy045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0074 (R : Class) :
    (nb092AlphaDummy003 R) ∈
      (((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy042 R)
            (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
              (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092AlphaDummy003 R) ≠ (nb092AlphaDummy042 R) from (by
          unfold nb092AlphaDummy042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092AlphaDummy003 R) ≠ (nb092AlphaDummy043 R) from (by
            unfold nb092AlphaDummy043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0075 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb092AlphaDummy044 x y)
            (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb092AlphaDummy044 x y) from (by
          unfold nb092AlphaDummy044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb092AlphaDummy045 x y) from (by
            unfold nb092AlphaDummy045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0076 (R : Class) :
    (nb092AlphaDummy043 R) ∈
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy043 R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0077 (x : Var) (y : Var) :
    (nb092AlphaDummy045 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb092AlphaDummy045 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0078 (R : Class) :
    (nb092AlphaDummy043 R) ∈
      (((synCphi (Class.cv (nb092AlphaDummy043 R)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy043 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0079 (x : Var) (y : Var) :
    (nb092AlphaDummy045 x y) ∈
      (((synCphi (Class.cv (nb092AlphaDummy045 x y)))).fv ∪
        ((synCphi (Class.cv (nb092AlphaDummy045 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
