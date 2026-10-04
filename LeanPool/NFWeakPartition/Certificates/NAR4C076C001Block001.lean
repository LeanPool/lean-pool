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

/-! Certificates from `NAR4C076C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_000`. -/
@[expose]
noncomputable def nb076AlphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_001`. -/
@[expose]
noncomputable def nb076AlphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_002`. -/
@[expose]
noncomputable def nb076AlphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_003`. -/
@[expose]
noncomputable def nb076AlphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_004`. -/
@[expose]
noncomputable def nb076AlphaDummy004 : Var :=
  (freshVar ((∅ : Finset Var)) 4)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_005`. -/
@[expose]
noncomputable def nb076AlphaDummy005 : Var :=
  (freshVar (({(nb076AlphaDummy003)} : Finset Var) ∪ ((synCncs)).fv ∪
          ({(nb076AlphaDummy004)} : Finset Var) ∪ ((synCncs)).fv ∪
      ((Class.cab (nb076AlphaDummy000)
          (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
            (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
              (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                (synCxp (Class.cv (nb076AlphaDummy001))
                  (Class.cv (nb076AlphaDummy002)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_006`. -/
@[expose]
noncomputable def nb076AlphaDummy006 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (({ m } : Finset Var) ∪ ((synCncs)).fv ∪ ({ n } : Finset Var) ∪ ((synCncs)).fv ∪
      ((Class.cab a (synWrex b (Class.cv m) (synWrex g (Class.cv n)
              (synWbr (Class.cv a) (synCen) (synCxp (Class.cv b) (Class.cv g))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_007`. -/
@[expose]
noncomputable def nb076AlphaDummy007 : Var :=
  (freshVar
    (({(nb076AlphaDummy003)} : Finset Var) ∪ ({(nb076AlphaDummy004)} : Finset Var) ∪
        ({(nb076AlphaDummy005)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv (nb076AlphaDummy003)) (synCncs))
            (Wff.classMem (Class.cv (nb076AlphaDummy004)) (synCncs)))
          (Wff.classEq (Class.cv (nb076AlphaDummy005)) (Class.cab (nb076AlphaDummy000)
              (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
                (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                  (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                    (synCxp (Class.cv (nb076AlphaDummy001))
                      (Class.cv (nb076AlphaDummy002)))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_008`. -/
@[expose]
noncomputable def nb076AlphaDummy008 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
        ({(nb076AlphaDummy006 g m n a b)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv m) (synCncs)) (Wff.classMem (Class.cv n) (synCncs)))
          (Wff.classEq (Class.cv (nb076AlphaDummy006 g m n a b)) (Class.cab a
              (synWrex b (Class.cv m) (synWrex g (Class.cv n) (synWbr (Class.cv a) (synCen)
                    (synCxp (Class.cv b) (Class.cv g))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_009`. -/
@[expose]
noncomputable def nb076AlphaDummy009 : Var :=
  (freshVar (((synCop (Class.cv (nb076AlphaDummy003))
          (Class.cv (nb076AlphaDummy004)))).fv ∪ ((Class.cv (nb076AlphaDummy005))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_010`. -/
@[expose]
noncomputable def nb076AlphaDummy010 : Var :=
  (freshVar (((synCop (Class.cv (nb076AlphaDummy003))
          (Class.cv (nb076AlphaDummy004)))).fv ∪ ((Class.cv (nb076AlphaDummy005))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_011`. -/
@[expose]
noncomputable def nb076AlphaDummy011 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((synCop (Class.cv m) (Class.cv n))).fv ∪
      ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_012`. -/
@[expose]
noncomputable def nb076AlphaDummy012 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((synCop (Class.cv m) (Class.cv n))).fv ∪
      ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_013`. -/
@[expose]
noncomputable def nb076AlphaDummy013 : Var :=
  (freshVar (((synCcompl (Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010)))))))).fv ∪ ((synCcompl
          (Class.cab (nb076AlphaDummy009)
            (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_014`. -/
@[expose]
noncomputable def nb076AlphaDummy014 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))))))).fv ∪ ((synCcompl
          (Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b)
              (Class.cv (nb076AlphaDummy006 g m n a b))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_015`. -/
@[expose]
noncomputable def nb076AlphaDummy015 : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
            (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
            (Wff.classEq (Class.cv (nb076AlphaDummy009))
              (synCphi (Class.cv (nb076AlphaDummy010))))))).fv ∪
      ((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
            (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
            (Wff.classEq (Class.cv (nb076AlphaDummy009))
              (synCphi (Class.cv (nb076AlphaDummy010))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_016`. -/
@[expose]
noncomputable def nb076AlphaDummy016 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy011 g m n a b)
          (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
            (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
              (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv ∪
      ((Class.cab (nb076AlphaDummy011 g m n a b)
          (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
            (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
              (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_017`. -/
@[expose]
noncomputable def nb076AlphaDummy017 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_018`. -/
@[expose]
noncomputable def nb076AlphaDummy018 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_019`. -/
@[expose]
noncomputable def nb076AlphaDummy019 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_020`. -/
@[expose]
noncomputable def nb076AlphaDummy020 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_021`. -/
@[expose]
noncomputable def nb076AlphaDummy021 : Var :=
  (freshVar (((synCcompl (Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCphi (Class.cv (nb076AlphaDummy018)))))))).fv ∪ ((synCcompl
          (Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_022`. -/
@[expose]
noncomputable def nb076AlphaDummy022 (m : Var) (n : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCphi (Class.cv (nb076AlphaDummy020 m n)))))))).fv ∪ ((synCcompl
          (Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_023`. -/
@[expose]
noncomputable def nb076AlphaDummy023 : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy017)
          (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
            (Wff.classEq (Class.cv (nb076AlphaDummy017))
              (synCphi (Class.cv (nb076AlphaDummy018))))))).fv ∪
      ((Class.cab (nb076AlphaDummy017)
          (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
            (Wff.classEq (Class.cv (nb076AlphaDummy017))
              (synCphi (Class.cv (nb076AlphaDummy018))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_024`. -/
@[expose]
noncomputable def nb076AlphaDummy024 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy019 m n)
          (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
            (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
              (synCphi (Class.cv (nb076AlphaDummy020 m n))))))).fv ∪
      ((Class.cab (nb076AlphaDummy019 m n) (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
            (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
              (synCphi (Class.cv (nb076AlphaDummy020 m n))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_025`. -/
@[expose]
noncomputable def nb076AlphaDummy025 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy018))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_026`. -/
@[expose]
noncomputable def nb076AlphaDummy026 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy018))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_027`. -/
@[expose]
noncomputable def nb076AlphaDummy027 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy020 m n))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_028`. -/
@[expose]
noncomputable def nb076AlphaDummy028 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy020 m n))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_029`. -/
@[expose]
noncomputable def nb076AlphaDummy029 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076AlphaDummy025)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb076AlphaDummy025)) (synC1c))).fv ∪
      ((Class.cv (nb076AlphaDummy025))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_030`. -/
@[expose]
noncomputable def nb076AlphaDummy030 (m : Var) (n : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076AlphaDummy027 m n)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb076AlphaDummy027 m n)) (synC1c))).fv ∪
      ((Class.cv (nb076AlphaDummy027 m n))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_031`. -/
@[expose]
noncomputable def nb076AlphaDummy031 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_032`. -/
@[expose]
noncomputable def nb076AlphaDummy032 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_033`. -/
@[expose]
noncomputable def nb076AlphaDummy033 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_034`. -/
@[expose]
noncomputable def nb076AlphaDummy034 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_035`. -/
@[expose]
noncomputable def nb076AlphaDummy035 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_036`. -/
@[expose]
noncomputable def nb076AlphaDummy036 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_037`. -/
@[expose]
noncomputable def nb076AlphaDummy037 : Var :=
  (freshVar (((synCnin (Class.cv (nb076AlphaDummy032))
          (Class.cv (nb076AlphaDummy033)))).fv ∪
      ((synCnin (Class.cv (nb076AlphaDummy032)) (Class.cv (nb076AlphaDummy033)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_038`. -/
@[expose]
noncomputable def nb076AlphaDummy038 (m : Var) (n : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb076AlphaDummy035 m n))
          (Class.cv (nb076AlphaDummy036 m n)))).fv ∪
      ((synCnin (Class.cv (nb076AlphaDummy035 m n))
          (Class.cv (nb076AlphaDummy036 m n)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_039`. -/
@[expose]
noncomputable def nb076AlphaDummy039 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_040`. -/
@[expose]
noncomputable def nb076AlphaDummy040 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
      ((Class.cv (nb076AlphaDummy036 m n))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_041`. -/
@[expose]
noncomputable def nb076AlphaDummy041 : Var :=
  (freshVar (((synCcompl (Class.cv (nb076AlphaDummy032)))).fv ∪
      ((synCcompl (Class.cv (nb076AlphaDummy033)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_042`. -/
@[expose]
noncomputable def nb076AlphaDummy042 (m : Var) (n : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb076AlphaDummy035 m n)))).fv ∪
      ((synCcompl (Class.cv (nb076AlphaDummy036 m n)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_043`. -/
@[expose]
noncomputable def nb076AlphaDummy043 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy032))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_044`. -/
@[expose]
noncomputable def nb076AlphaDummy044 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
      ((Class.cv (nb076AlphaDummy035 m n))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_045`. -/
@[expose]
noncomputable def nb076AlphaDummy045 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy033))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_046`. -/
@[expose]
noncomputable def nb076AlphaDummy046 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy036 m n))).fv ∪
      ((Class.cv (nb076AlphaDummy036 m n))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_047`. -/
@[expose]
noncomputable def nb076AlphaDummy047 : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy017)
          (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
            (Wff.classEq (Class.cv (nb076AlphaDummy017))
              (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy017)
          (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
            (Wff.classEq (Class.cv (nb076AlphaDummy017))
              (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_048`. -/
@[expose]
noncomputable def nb076AlphaDummy048 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy019 m n)
          (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
            (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
              (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy019 m n)
          (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
            (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
              (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_049`. -/
@[expose]
noncomputable def nb076AlphaDummy049 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb076AlphaDummy018))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_050`. -/
@[expose]
noncomputable def nb076AlphaDummy050 (m : Var) (n : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb076AlphaDummy020 m n))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_051`. -/
@[expose]
noncomputable def nb076AlphaDummy051 : Var :=
  (freshVar (((synCphi (Class.cv (nb076AlphaDummy018)))).fv ∪
      ((synCphi (Class.cv (nb076AlphaDummy018)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_052`. -/
@[expose]
noncomputable def nb076AlphaDummy052 (m : Var) (n : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb076AlphaDummy020 m n)))).fv ∪
      ((synCphi (Class.cv (nb076AlphaDummy020 m n)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_053`. -/
@[expose]
noncomputable def nb076AlphaDummy053 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy010))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_054`. -/
@[expose]
noncomputable def nb076AlphaDummy054 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy010))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_055`. -/
@[expose]
noncomputable def nb076AlphaDummy055 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_056`. -/
@[expose]
noncomputable def nb076AlphaDummy056 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_057`. -/
@[expose]
noncomputable def nb076AlphaDummy057 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076AlphaDummy053)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb076AlphaDummy053)) (synC1c))).fv ∪
      ((Class.cv (nb076AlphaDummy053))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_058`. -/
@[expose]
noncomputable def nb076AlphaDummy058 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076AlphaDummy055 g m n a b)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb076AlphaDummy055 g m n a b)) (synC1c))).fv ∪
      ((Class.cv (nb076AlphaDummy055 g m n a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_059`. -/
@[expose]
noncomputable def nb076AlphaDummy059 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_060`. -/
@[expose]
noncomputable def nb076AlphaDummy060 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_061`. -/
@[expose]
noncomputable def nb076AlphaDummy061 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_062`. -/
@[expose]
noncomputable def nb076AlphaDummy062 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_063`. -/
@[expose]
noncomputable def nb076AlphaDummy063 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_064`. -/
@[expose]
noncomputable def nb076AlphaDummy064 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_065`. -/
@[expose]
noncomputable def nb076AlphaDummy065 : Var :=
  (freshVar (((synCnin (Class.cv (nb076AlphaDummy060))
          (Class.cv (nb076AlphaDummy061)))).fv ∪
      ((synCnin (Class.cv (nb076AlphaDummy060)) (Class.cv (nb076AlphaDummy061)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_066`. -/
@[expose]
noncomputable def nb076AlphaDummy066 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
          (Class.cv (nb076AlphaDummy064 g m n a b)))).fv ∪
      ((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
          (Class.cv (nb076AlphaDummy064 g m n a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_067`. -/
@[expose]
noncomputable def nb076AlphaDummy067 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_068`. -/
@[expose]
noncomputable def nb076AlphaDummy068 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
      ((Class.cv (nb076AlphaDummy064 g m n a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_069`. -/
@[expose]
noncomputable def nb076AlphaDummy069 : Var :=
  (freshVar (((synCcompl (Class.cv (nb076AlphaDummy060)))).fv ∪
      ((synCcompl (Class.cv (nb076AlphaDummy061)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_070`. -/
@[expose]
noncomputable def nb076AlphaDummy070 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb076AlphaDummy063 g m n a b)))).fv ∪
      ((synCcompl (Class.cv (nb076AlphaDummy064 g m n a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_071`. -/
@[expose]
noncomputable def nb076AlphaDummy071 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy060))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_072`. -/
@[expose]
noncomputable def nb076AlphaDummy072 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
      ((Class.cv (nb076AlphaDummy063 g m n a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_073`. -/
@[expose]
noncomputable def nb076AlphaDummy073 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy061))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_074`. -/
@[expose]
noncomputable def nb076AlphaDummy074 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy064 g m n a b))).fv ∪
      ((Class.cv (nb076AlphaDummy064 g m n a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_075`. -/
@[expose]
noncomputable def nb076AlphaDummy075 : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy009)
          (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
            (Wff.classEq (Class.cv (nb076AlphaDummy009))
              (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy009)
          (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
            (Wff.classEq (Class.cv (nb076AlphaDummy009))
              (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_076`. -/
@[expose]
noncomputable def nb076AlphaDummy076 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy011 g m n a b)
          (synWrex (nb076AlphaDummy012 g m n a b)
            (Class.cv (nb076AlphaDummy006 g m n a b))
            (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
              (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy011 g m n a b)
          (synWrex (nb076AlphaDummy012 g m n a b)
            (Class.cv (nb076AlphaDummy006 g m n a b))
            (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
              (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_077`. -/
@[expose]
noncomputable def nb076AlphaDummy077 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb076AlphaDummy010))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_078`. -/
@[expose]
noncomputable def nb076AlphaDummy078 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_079`. -/
@[expose]
noncomputable def nb076AlphaDummy079 : Var :=
  (freshVar (((synCphi (Class.cv (nb076AlphaDummy010)))).fv ∪
      ((synCphi (Class.cv (nb076AlphaDummy010)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_080`. -/
@[expose]
noncomputable def nb076AlphaDummy080 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))).fv ∪
      ((synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_081`. -/
@[expose]
noncomputable def nb076AlphaDummy081 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy000))).fv ∪
      ((synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_082`. -/
@[expose]
noncomputable def nb076AlphaDummy082 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy000))).fv ∪
      ((synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_083`. -/
@[expose]
noncomputable def nb076AlphaDummy083 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_084`. -/
@[expose]
noncomputable def nb076AlphaDummy084 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_085`. -/
@[expose]
noncomputable def nb076AlphaDummy085 : Var :=
  (freshVar (((synCcompl (Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCphi (Class.cv (nb076AlphaDummy082)))))))).fv ∪ ((synCcompl
          (Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
              (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_086`. -/
@[expose]
noncomputable def nb076AlphaDummy086 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCphi (Class.cv (nb076AlphaDummy084 g a b)))))))).fv ∪ ((synCcompl
          (Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_087`. -/
@[expose]
noncomputable def nb076AlphaDummy087 : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy081)
          (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
            (Wff.classEq (Class.cv (nb076AlphaDummy081))
              (synCphi (Class.cv (nb076AlphaDummy082))))))).fv ∪
      ((Class.cab (nb076AlphaDummy081)
          (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
            (Wff.classEq (Class.cv (nb076AlphaDummy081))
              (synCphi (Class.cv (nb076AlphaDummy082))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_088`. -/
@[expose]
noncomputable def nb076AlphaDummy088 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy083 g a b)
          (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
              (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))).fv ∪
      ((Class.cab (nb076AlphaDummy083 g a b)
          (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
              (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_089`. -/
@[expose]
noncomputable def nb076AlphaDummy089 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy082))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_090`. -/
@[expose]
noncomputable def nb076AlphaDummy090 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy082))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_091`. -/
@[expose]
noncomputable def nb076AlphaDummy091 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy084 g a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_092`. -/
@[expose]
noncomputable def nb076AlphaDummy092 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy084 g a b))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_093`. -/
@[expose]
noncomputable def nb076AlphaDummy093 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076AlphaDummy089)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb076AlphaDummy089)) (synC1c))).fv ∪
      ((Class.cv (nb076AlphaDummy089))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_094`. -/
@[expose]
noncomputable def nb076AlphaDummy094 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076AlphaDummy091 g a b)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb076AlphaDummy091 g a b)) (synC1c))).fv ∪
      ((Class.cv (nb076AlphaDummy091 g a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_095`. -/
@[expose]
noncomputable def nb076AlphaDummy095 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_096`. -/
@[expose]
noncomputable def nb076AlphaDummy096 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_097`. -/
@[expose]
noncomputable def nb076AlphaDummy097 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_098`. -/
@[expose]
noncomputable def nb076AlphaDummy098 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_099`. -/
@[expose]
noncomputable def nb076AlphaDummy099 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_100`. -/
@[expose]
noncomputable def nb076AlphaDummy100 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_101`. -/
@[expose]
noncomputable def nb076AlphaDummy101 : Var :=
  (freshVar (((synCnin (Class.cv (nb076AlphaDummy096))
          (Class.cv (nb076AlphaDummy097)))).fv ∪
      ((synCnin (Class.cv (nb076AlphaDummy096)) (Class.cv (nb076AlphaDummy097)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_102`. -/
@[expose]
noncomputable def nb076AlphaDummy102 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb076AlphaDummy099 g a b))
          (Class.cv (nb076AlphaDummy100 g a b)))).fv ∪
      ((synCnin (Class.cv (nb076AlphaDummy099 g a b))
          (Class.cv (nb076AlphaDummy100 g a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_103`. -/
@[expose]
noncomputable def nb076AlphaDummy103 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_104`. -/
@[expose]
noncomputable def nb076AlphaDummy104 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
      ((Class.cv (nb076AlphaDummy100 g a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_105`. -/
@[expose]
noncomputable def nb076AlphaDummy105 : Var :=
  (freshVar (((synCcompl (Class.cv (nb076AlphaDummy096)))).fv ∪
      ((synCcompl (Class.cv (nb076AlphaDummy097)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_106`. -/
@[expose]
noncomputable def nb076AlphaDummy106 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb076AlphaDummy099 g a b)))).fv ∪
      ((synCcompl (Class.cv (nb076AlphaDummy100 g a b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_107`. -/
@[expose]
noncomputable def nb076AlphaDummy107 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy096))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_108`. -/
@[expose]
noncomputable def nb076AlphaDummy108 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
      ((Class.cv (nb076AlphaDummy099 g a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_109`. -/
@[expose]
noncomputable def nb076AlphaDummy109 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy097))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_110`. -/
@[expose]
noncomputable def nb076AlphaDummy110 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy100 g a b))).fv ∪
      ((Class.cv (nb076AlphaDummy100 g a b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_111`. -/
@[expose]
noncomputable def nb076AlphaDummy111 : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
            (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
            (Wff.classEq (Class.cv (nb076AlphaDummy081))
              (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy081)
          (synWrex (nb076AlphaDummy082) (synCxp (Class.cv (nb076AlphaDummy001))
              (Class.cv (nb076AlphaDummy002)))
            (Wff.classEq (Class.cv (nb076AlphaDummy081))
              (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_112`. -/
@[expose]
noncomputable def nb076AlphaDummy112 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy083 g a b)
          (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
            (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
              (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy083 g a b)
          (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
            (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
              (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_113`. -/
@[expose]
noncomputable def nb076AlphaDummy113 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_114`. -/
@[expose]
noncomputable def nb076AlphaDummy114 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_115`. -/
@[expose]
noncomputable def nb076AlphaDummy115 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_116`. -/
@[expose]
noncomputable def nb076AlphaDummy116 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_117`. -/
@[expose]
noncomputable def nb076AlphaDummy117 : Var :=
  (freshVar
    (({(nb076AlphaDummy113)} : Finset Var) ∪ ({(nb076AlphaDummy114)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy113))
            (Class.cv (nb076AlphaDummy001))) (Wff.classMem (Class.cv (nb076AlphaDummy114))
            (Class.cv (nb076AlphaDummy002))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_118`. -/
@[expose]
noncomputable def nb076AlphaDummy118 (g : Var) (b : Var) : Var :=
  (freshVar (({(nb076AlphaDummy115 g b)} : Finset Var) ∪
        ({(nb076AlphaDummy116 g b)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy115 g b)) (Class.cv b))
          (Wff.classMem (Class.cv (nb076AlphaDummy116 g b)) (Class.cv g)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_119`. -/
@[expose]
noncomputable def nb076AlphaDummy119 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_120`. -/
@[expose]
noncomputable def nb076AlphaDummy120 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_121`. -/
@[expose]
noncomputable def nb076AlphaDummy121 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
      ((Class.cv (nb076AlphaDummy116 g b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_122`. -/
@[expose]
noncomputable def nb076AlphaDummy122 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
      ((Class.cv (nb076AlphaDummy116 g b))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_123`. -/
@[expose]
noncomputable def nb076AlphaDummy123 : Var :=
  (freshVar (((synCcompl (Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCphi (Class.cv (nb076AlphaDummy120)))))))).fv ∪ ((synCcompl
          (Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_124`. -/
@[expose]
noncomputable def nb076AlphaDummy124 (g : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCphi (Class.cv (nb076AlphaDummy122 g b)))))))).fv ∪ ((synCcompl
          (Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_125`. -/
@[expose]
noncomputable def nb076AlphaDummy125 : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy119)
          (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
            (Wff.classEq (Class.cv (nb076AlphaDummy119))
              (synCphi (Class.cv (nb076AlphaDummy120))))))).fv ∪
      ((Class.cab (nb076AlphaDummy119)
          (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
            (Wff.classEq (Class.cv (nb076AlphaDummy119))
              (synCphi (Class.cv (nb076AlphaDummy120))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_126`. -/
@[expose]
noncomputable def nb076AlphaDummy126 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy121 g b)
          (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
            (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
              (synCphi (Class.cv (nb076AlphaDummy122 g b))))))).fv ∪
      ((Class.cab (nb076AlphaDummy121 g b)
          (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
            (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
              (synCphi (Class.cv (nb076AlphaDummy122 g b))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_127`. -/
@[expose]
noncomputable def nb076AlphaDummy127 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy120))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_128`. -/
@[expose]
noncomputable def nb076AlphaDummy128 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy120))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_129`. -/
@[expose]
noncomputable def nb076AlphaDummy129 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy122 g b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_130`. -/
@[expose]
noncomputable def nb076AlphaDummy130 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy122 g b))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_131`. -/
@[expose]
noncomputable def nb076AlphaDummy131 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076AlphaDummy127)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb076AlphaDummy127)) (synC1c))).fv ∪
      ((Class.cv (nb076AlphaDummy127))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_132`. -/
@[expose]
noncomputable def nb076AlphaDummy132 (g : Var) (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076AlphaDummy129 g b)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb076AlphaDummy129 g b)) (synC1c))).fv ∪
      ((Class.cv (nb076AlphaDummy129 g b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_133`. -/
@[expose]
noncomputable def nb076AlphaDummy133 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_134`. -/
@[expose]
noncomputable def nb076AlphaDummy134 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_135`. -/
@[expose]
noncomputable def nb076AlphaDummy135 : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_136`. -/
@[expose]
noncomputable def nb076AlphaDummy136 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_137`. -/
@[expose]
noncomputable def nb076AlphaDummy137 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_138`. -/
@[expose]
noncomputable def nb076AlphaDummy138 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_139`. -/
@[expose]
noncomputable def nb076AlphaDummy139 : Var :=
  (freshVar (((synCnin (Class.cv (nb076AlphaDummy134))
          (Class.cv (nb076AlphaDummy135)))).fv ∪
      ((synCnin (Class.cv (nb076AlphaDummy134)) (Class.cv (nb076AlphaDummy135)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_140`. -/
@[expose]
noncomputable def nb076AlphaDummy140 (g : Var) (b : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb076AlphaDummy137 g b))
          (Class.cv (nb076AlphaDummy138 g b)))).fv ∪
      ((synCnin (Class.cv (nb076AlphaDummy137 g b))
          (Class.cv (nb076AlphaDummy138 g b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_141`. -/
@[expose]
noncomputable def nb076AlphaDummy141 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_142`. -/
@[expose]
noncomputable def nb076AlphaDummy142 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
      ((Class.cv (nb076AlphaDummy138 g b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_143`. -/
@[expose]
noncomputable def nb076AlphaDummy143 : Var :=
  (freshVar (((synCcompl (Class.cv (nb076AlphaDummy134)))).fv ∪
      ((synCcompl (Class.cv (nb076AlphaDummy135)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_144`. -/
@[expose]
noncomputable def nb076AlphaDummy144 (g : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb076AlphaDummy137 g b)))).fv ∪
      ((synCcompl (Class.cv (nb076AlphaDummy138 g b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_145`. -/
@[expose]
noncomputable def nb076AlphaDummy145 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy134))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_146`. -/
@[expose]
noncomputable def nb076AlphaDummy146 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
      ((Class.cv (nb076AlphaDummy137 g b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_147`. -/
@[expose]
noncomputable def nb076AlphaDummy147 : Var :=
  (freshVar
    (((Class.cv (nb076AlphaDummy135))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_148`. -/
@[expose]
noncomputable def nb076AlphaDummy148 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076AlphaDummy138 g b))).fv ∪
      ((Class.cv (nb076AlphaDummy138 g b))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_149`. -/
@[expose]
noncomputable def nb076AlphaDummy149 : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy119)
          (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
            (Wff.classEq (Class.cv (nb076AlphaDummy119))
              (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy119)
          (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
            (Wff.classEq (Class.cv (nb076AlphaDummy119))
              (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                (synCsn (synC0c))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_150`. -/
@[expose]
noncomputable def nb076AlphaDummy150 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb076AlphaDummy121 g b)
          (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
            (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
              (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy121 g b)
          (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
            (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
              (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_151`. -/
@[expose]
noncomputable def nb076AlphaDummy151 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb076AlphaDummy120))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_152`. -/
@[expose]
noncomputable def nb076AlphaDummy152 (g : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb076AlphaDummy122 g b))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_153`. -/
@[expose]
noncomputable def nb076AlphaDummy153 : Var :=
  (freshVar (((synCphi (Class.cv (nb076AlphaDummy120)))).fv ∪
      ((synCphi (Class.cv (nb076AlphaDummy120)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_154`. -/
@[expose]
noncomputable def nb076AlphaDummy154 (g : Var) (b : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb076AlphaDummy122 g b)))).fv ∪
      ((synCphi (Class.cv (nb076AlphaDummy122 g b)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_155`. -/
@[expose]
noncomputable def nb076AlphaDummy155 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb076AlphaDummy082))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_156`. -/
@[expose]
noncomputable def nb076AlphaDummy156 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb076AlphaDummy084 g a b))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_157`. -/
@[expose]
noncomputable def nb076AlphaDummy157 : Var :=
  (freshVar (((synCphi (Class.cv (nb076AlphaDummy082)))).fv ∪
      ((synCphi (Class.cv (nb076AlphaDummy082)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb076_alpha_dummy_158`. -/
@[expose]
noncomputable def nb076AlphaDummy158 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb076AlphaDummy084 g a b)))).fv ∪
      ((synCphi (Class.cv (nb076AlphaDummy084 g a b)))).fv) 0)

theorem nb076_fresh_000 :
    (nb076AlphaDummy075) ∉
      (((Class.cab (nb076AlphaDummy009)
            (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy009)
            (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb076AlphaDummy075] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy009)
            (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy009)
            (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb076_fresh_001 :
    (nb076AlphaDummy015) ∉
      (((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))).fv ∪
        ((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))).fv) :=
  by
  simpa only [nb076AlphaDummy015] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))).fv ∪
        ((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))).fv)
      0

theorem nb076_fresh_002 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy076 g m n a b) ∉
      (((Class.cab (nb076AlphaDummy011 g m n a b) (synWrex (nb076AlphaDummy012 g m n a b)
              (Class.cv (nb076AlphaDummy006 g m n a b))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b)
              (Class.cv (nb076AlphaDummy006 g m n a b))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb076AlphaDummy076] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy011 g m n a b) (synWrex (nb076AlphaDummy012 g m n a b)
              (Class.cv (nb076AlphaDummy006 g m n a b))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b)
              (Class.cv (nb076AlphaDummy006 g m n a b))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb076_fresh_003 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy016 g m n a b) ∉
      (((Class.cab (nb076AlphaDummy011 g m n a b) (synWrex (nb076AlphaDummy012 g m n a b)
              (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv) :=
  by
  simpa only [nb076AlphaDummy016] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy011 g m n a b) (synWrex (nb076AlphaDummy012 g m n a b)
              (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv)
      0

theorem nb076_fresh_004 :
    (nb076AlphaDummy023) ∉
      (((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCphi (Class.cv (nb076AlphaDummy018))))))).fv ∪
        ((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCphi (Class.cv (nb076AlphaDummy018))))))).fv) :=
  by
  simpa only [nb076AlphaDummy023] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCphi (Class.cv (nb076AlphaDummy018))))))).fv ∪
        ((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCphi (Class.cv (nb076AlphaDummy018))))))).fv)
      0

theorem nb076_fresh_005 :
    (nb076AlphaDummy047) ∉
      (((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb076AlphaDummy047] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb076_fresh_006 (m : Var) (n : Var) :
    (nb076AlphaDummy024 m n) ∉
      (((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCphi (Class.cv (nb076AlphaDummy020 m n))))))).fv ∪
        ((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCphi (Class.cv (nb076AlphaDummy020 m n))))))).fv) :=
  by
  simpa only [nb076AlphaDummy024] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCphi (Class.cv (nb076AlphaDummy020 m n))))))).fv ∪
        ((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCphi (Class.cv (nb076AlphaDummy020 m n))))))).fv)
      0

theorem nb076_fresh_007 (m : Var) (n : Var) :
    (nb076AlphaDummy048 m n) ∉
      (((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb076AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb076_fresh_008 :
    (nb076AlphaDummy087) ∉
      (((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCphi (Class.cv (nb076AlphaDummy082))))))).fv ∪
        ((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCphi (Class.cv (nb076AlphaDummy082))))))).fv) :=
  by
  simpa only [nb076AlphaDummy087] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCphi (Class.cv (nb076AlphaDummy082))))))).fv ∪
        ((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCphi (Class.cv (nb076AlphaDummy082))))))).fv)
      0

theorem nb076_fresh_009 :
    (nb076AlphaDummy111) ∉
      (((Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
              (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (synCxp (Class.cv (nb076AlphaDummy001))
                (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb076AlphaDummy111] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
              (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (synCxp (Class.cv (nb076AlphaDummy001))
                (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb076_fresh_010 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy088 g a b) ∉
      (((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))).fv) :=
  by
  simpa only [nb076AlphaDummy088] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))).fv)
      0

theorem nb076_fresh_011 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy112 g a b) ∉
      (((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb076AlphaDummy112] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb076_fresh_012 :
    (nb076AlphaDummy125) ∉
      (((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCphi (Class.cv (nb076AlphaDummy120))))))).fv ∪
        ((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCphi (Class.cv (nb076AlphaDummy120))))))).fv) :=
  by
  simpa only [nb076AlphaDummy125] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCphi (Class.cv (nb076AlphaDummy120))))))).fv ∪
        ((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCphi (Class.cv (nb076AlphaDummy120))))))).fv)
      0

theorem nb076_fresh_013 :
    (nb076AlphaDummy149) ∉
      (((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb076AlphaDummy149] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb076_fresh_014 (g : Var) (b : Var) :
    (nb076AlphaDummy126 g b) ∉
      (((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCphi (Class.cv (nb076AlphaDummy122 g b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCphi (Class.cv (nb076AlphaDummy122 g b))))))).fv) :=
  by
  simpa only [nb076AlphaDummy126] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCphi (Class.cv (nb076AlphaDummy122 g b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCphi (Class.cv (nb076AlphaDummy122 g b))))))).fv)
      0

theorem nb076_fresh_015 (g : Var) (b : Var) :
    (nb076AlphaDummy150 g b) ∉
      (((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb076AlphaDummy150] using
    freshVar_not_mem
      (((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb076_fresh_016 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy083 g a b) ∉
      (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) :=
  by
  simpa only [nb076AlphaDummy083] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) 0

theorem nb076_fresh_017 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy084 g a b) ∉
      (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) :=
  by
  simpa only [nb076AlphaDummy084] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) 1

theorem nb076_distinct_018 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy083 g a b) ≠ (nb076AlphaDummy084 g a b) := by
  simpa only [nb076AlphaDummy083, nb076AlphaDummy084] using
    (freshVar_injective (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_019 :
    (nb076AlphaDummy081) ∉
      (((Class.cv (nb076AlphaDummy000))).fv ∪ ((synCxp (Class.cv (nb076AlphaDummy001))
            (Class.cv (nb076AlphaDummy002)))).fv) :=
  by
  simpa only [nb076AlphaDummy081] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy000))).fv ∪ ((synCxp (Class.cv (nb076AlphaDummy001))
            (Class.cv (nb076AlphaDummy002)))).fv)
      0

theorem nb076_fresh_020 :
    (nb076AlphaDummy082) ∉
      (((Class.cv (nb076AlphaDummy000))).fv ∪ ((synCxp (Class.cv (nb076AlphaDummy001))
            (Class.cv (nb076AlphaDummy002)))).fv) :=
  by
  simpa only [nb076AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy000))).fv ∪ ((synCxp (Class.cv (nb076AlphaDummy001))
            (Class.cv (nb076AlphaDummy002)))).fv)
      1

theorem nb076_distinct_021 : (nb076AlphaDummy081) ≠ (nb076AlphaDummy082) := by
  simpa only [nb076AlphaDummy081, nb076AlphaDummy082] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy000))).fv ∪
        ((synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_022 :
    (nb076AlphaDummy113) ∉
      (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv) :=
  by
  simpa only [nb076AlphaDummy113] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv)
      0

theorem nb076_fresh_023 :
    (nb076AlphaDummy114) ∉
      (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv) :=
  by
  simpa only [nb076AlphaDummy114] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv)
      1

theorem nb076_distinct_024 : (nb076AlphaDummy113) ≠ (nb076AlphaDummy114) := by
  simpa only [nb076AlphaDummy113, nb076AlphaDummy114] using
    (freshVar_injective
      (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_025 :
    (nb076AlphaDummy017) ∉
      (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv) :=
  by
  simpa only [nb076AlphaDummy017] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv)
      0

theorem nb076_fresh_026 :
    (nb076AlphaDummy018) ∉
      (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv) :=
  by
  simpa only [nb076AlphaDummy018] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv)
      1

theorem nb076_distinct_027 : (nb076AlphaDummy017) ≠ (nb076AlphaDummy018) := by
  simpa only [nb076AlphaDummy017, nb076AlphaDummy018] using
    (freshVar_injective
      (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_028 :
    (nb076AlphaDummy053) ∉ (((Class.cv (nb076AlphaDummy010))).fv) := by
  simpa only [nb076AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy010))).fv) 0

theorem nb076_fresh_029 :
    (nb076AlphaDummy054) ∉ (((Class.cv (nb076AlphaDummy010))).fv) := by
  simpa only [nb076AlphaDummy054] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy010))).fv) 1

theorem nb076_distinct_030 : (nb076AlphaDummy053) ≠ (nb076AlphaDummy054) := by
  simpa only [nb076AlphaDummy053, nb076AlphaDummy054] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy010))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_031 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy055 g m n a b) ∉
      (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) :=
  by
  simpa only [nb076AlphaDummy055] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) 0

theorem nb076_fresh_032 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy056 g m n a b) ∉
      (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) :=
  by
  simpa only [nb076AlphaDummy056] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) 1

theorem nb076_distinct_033 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy055 g m n a b) ≠ (nb076AlphaDummy056 g m n a b) := by
  simpa only [nb076AlphaDummy055, nb076AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb076_fresh_034 :
    (nb076AlphaDummy025) ∉ (((Class.cv (nb076AlphaDummy018))).fv) := by
  simpa only [nb076AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy018))).fv) 0

theorem nb076_fresh_035 :
    (nb076AlphaDummy026) ∉ (((Class.cv (nb076AlphaDummy018))).fv) := by
  simpa only [nb076AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy018))).fv) 1

theorem nb076_distinct_036 : (nb076AlphaDummy025) ≠ (nb076AlphaDummy026) := by
  simpa only [nb076AlphaDummy025, nb076AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy018))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_037 (m : Var) (n : Var) :
    (nb076AlphaDummy027 m n) ∉ (((Class.cv (nb076AlphaDummy020 m n))).fv) := by
  simpa only [nb076AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy020 m n))).fv) 0

theorem nb076_fresh_038 (m : Var) (n : Var) :
    (nb076AlphaDummy028 m n) ∉ (((Class.cv (nb076AlphaDummy020 m n))).fv) := by
  simpa only [nb076AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy020 m n))).fv) 1

theorem nb076_distinct_039 (m : Var) (n : Var) :
    (nb076AlphaDummy027 m n) ≠ (nb076AlphaDummy028 m n) := by
  simpa only [nb076AlphaDummy027, nb076AlphaDummy028] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy020 m n))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb076_fresh_040 :
    (nb076AlphaDummy031) ∉
      (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) 0

theorem nb076_fresh_041 :
    (nb076AlphaDummy032) ∉
      (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) 1

theorem nb076_fresh_042 :
    (nb076AlphaDummy033) ∉
      (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) 2

theorem nb076_distinct_043 : (nb076AlphaDummy031) ≠ (nb076AlphaDummy032) := by
  simpa only [nb076AlphaDummy031, nb076AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb076_distinct_044 : (nb076AlphaDummy031) ≠ (nb076AlphaDummy033) := by
  simpa only [nb076AlphaDummy031, nb076AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb076_distinct_045 : (nb076AlphaDummy032) ≠ (nb076AlphaDummy033) := by
  simpa only [nb076AlphaDummy032, nb076AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb076_fresh_046 (m : Var) (n : Var) :
    (nb076AlphaDummy034 m n) ∉
      (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy034] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) 0

theorem nb076_fresh_047 (m : Var) (n : Var) :
    (nb076AlphaDummy035 m n) ∉
      (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy035] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) 1

theorem nb076_fresh_048 (m : Var) (n : Var) :
    (nb076AlphaDummy036 m n) ∉
      (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy036] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) 2

theorem nb076_distinct_049 (m : Var) (n : Var) :
    (nb076AlphaDummy034 m n) ≠ (nb076AlphaDummy035 m n) := by
  simpa only [nb076AlphaDummy034, nb076AlphaDummy035] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_distinct_050 (m : Var) (n : Var) :
    (nb076AlphaDummy034 m n) ≠ (nb076AlphaDummy036 m n) := by
  simpa only [nb076AlphaDummy034, nb076AlphaDummy036] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb076_distinct_051 (m : Var) (n : Var) :
    (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy036 m n) := by
  simpa only [nb076AlphaDummy035, nb076AlphaDummy036] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb076_fresh_052 :
    (nb076AlphaDummy043) ∉
      (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy032))).fv) :=
  by
  simpa only [nb076AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy032))).fv)
      0

theorem nb076_fresh_053 :
    (nb076AlphaDummy039) ∉
      (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv) :=
  by
  simpa only [nb076AlphaDummy039] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv)
      0

theorem nb076_fresh_054 :
    (nb076AlphaDummy045) ∉
      (((Class.cv (nb076AlphaDummy033))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv) :=
  by
  simpa only [nb076AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy033))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv)
      0

theorem nb076_fresh_055 (m : Var) (n : Var) :
    (nb076AlphaDummy044 m n) ∉
      (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy035 m n))).fv) :=
  by
  simpa only [nb076AlphaDummy044] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy035 m n))).fv)
      0

theorem nb076_fresh_056 (m : Var) (n : Var) :
    (nb076AlphaDummy040 m n) ∉
      (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy036 m n))).fv) :=
  by
  simpa only [nb076AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy036 m n))).fv)
      0

theorem nb076_fresh_057 (m : Var) (n : Var) :
    (nb076AlphaDummy046 m n) ∉
      (((Class.cv (nb076AlphaDummy036 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy036 m n))).fv) :=
  by
  simpa only [nb076AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy036 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy036 m n))).fv)
      0

theorem nb076_fresh_058 :
    (nb076AlphaDummy059) ∉
      (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy059] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) 0

theorem nb076_fresh_059 :
    (nb076AlphaDummy060) ∉
      (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy060] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) 1

theorem nb076_fresh_060 :
    (nb076AlphaDummy061) ∉
      (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) 2

theorem nb076_distinct_061 : (nb076AlphaDummy059) ≠ (nb076AlphaDummy060) := by
  simpa only [nb076AlphaDummy059, nb076AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb076_distinct_062 : (nb076AlphaDummy059) ≠ (nb076AlphaDummy061) := by
  simpa only [nb076AlphaDummy059, nb076AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb076_distinct_063 : (nb076AlphaDummy060) ≠ (nb076AlphaDummy061) := by
  simpa only [nb076AlphaDummy060, nb076AlphaDummy061] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb076_fresh_064 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy062 g m n a b) ∉
      (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv)
      0

theorem nb076_fresh_065 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy063 g m n a b) ∉
      (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv)
      1

theorem nb076_fresh_066 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy064 g m n a b) ∉
      (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv)
      2

theorem nb076_distinct_067 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy062 g m n a b) ≠ (nb076AlphaDummy063 g m n a b) := by
  simpa only [nb076AlphaDummy062, nb076AlphaDummy063] using
    (freshVar_injective
      (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb076_distinct_068 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy062 g m n a b) ≠ (nb076AlphaDummy064 g m n a b) := by
  simpa only [nb076AlphaDummy062, nb076AlphaDummy064] using
    (freshVar_injective
      (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (i := 0) (j :=
      2) (by decide))

theorem nb076_distinct_069 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy064 g m n a b) := by
  simpa only [nb076AlphaDummy063, nb076AlphaDummy064] using
    (freshVar_injective
      (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (i := 1) (j :=
      2) (by decide))

theorem nb076_fresh_070 :
    (nb076AlphaDummy071) ∉
      (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy060))).fv) :=
  by
  simpa only [nb076AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy060))).fv)
      0

theorem nb076_fresh_071 :
    (nb076AlphaDummy067) ∉
      (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv) :=
  by
  simpa only [nb076AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv)
      0

theorem nb076_fresh_072 :
    (nb076AlphaDummy073) ∉
      (((Class.cv (nb076AlphaDummy061))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv) :=
  by
  simpa only [nb076AlphaDummy073] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy061))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv)
      0

theorem nb076_fresh_073 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy072 g m n a b) ∉
      (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy063 g m n a b))).fv) :=
  by
  simpa only [nb076AlphaDummy072] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy063 g m n a b))).fv)
      0

theorem nb076_fresh_074 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy068 g m n a b) ∉
      (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy064 g m n a b))).fv) :=
  by
  simpa only [nb076AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy064 g m n a b))).fv)
      0

theorem nb076_fresh_075 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy074 g m n a b) ∉
      (((Class.cv (nb076AlphaDummy064 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy064 g m n a b))).fv) :=
  by
  simpa only [nb076AlphaDummy074] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy064 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy064 g m n a b))).fv)
      0

theorem nb076_fresh_076 :
    (nb076AlphaDummy089) ∉ (((Class.cv (nb076AlphaDummy082))).fv) := by
  simpa only [nb076AlphaDummy089] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy082))).fv) 0

theorem nb076_fresh_077 :
    (nb076AlphaDummy090) ∉ (((Class.cv (nb076AlphaDummy082))).fv) := by
  simpa only [nb076AlphaDummy090] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy082))).fv) 1

theorem nb076_distinct_078 : (nb076AlphaDummy089) ≠ (nb076AlphaDummy090) := by
  simpa only [nb076AlphaDummy089, nb076AlphaDummy090] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy082))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_079 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy091 g a b) ∉ (((Class.cv (nb076AlphaDummy084 g a b))).fv) := by
  simpa only [nb076AlphaDummy091] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy084 g a b))).fv) 0

theorem nb076_fresh_080 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy092 g a b) ∉ (((Class.cv (nb076AlphaDummy084 g a b))).fv) := by
  simpa only [nb076AlphaDummy092] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy084 g a b))).fv) 1

theorem nb076_distinct_081 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy091 g a b) ≠ (nb076AlphaDummy092 g a b) := by
  simpa only [nb076AlphaDummy091, nb076AlphaDummy092] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy084 g a b))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb076_fresh_082 :
    (nb076AlphaDummy095) ∉
      (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy095] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) 0

theorem nb076_fresh_083 :
    (nb076AlphaDummy096) ∉
      (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy096] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) 1

theorem nb076_fresh_084 :
    (nb076AlphaDummy097) ∉
      (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy097] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) 2

theorem nb076_distinct_085 : (nb076AlphaDummy095) ≠ (nb076AlphaDummy096) := by
  simpa only [nb076AlphaDummy095, nb076AlphaDummy096] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb076_distinct_086 : (nb076AlphaDummy095) ≠ (nb076AlphaDummy097) := by
  simpa only [nb076AlphaDummy095, nb076AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb076_distinct_087 : (nb076AlphaDummy096) ≠ (nb076AlphaDummy097) := by
  simpa only [nb076AlphaDummy096, nb076AlphaDummy097] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb076_fresh_088 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy098 g a b) ∉
      (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy098] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) 0

theorem nb076_fresh_089 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy099 g a b) ∉
      (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy099] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) 1

theorem nb076_fresh_090 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy100 g a b) ∉
      (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy100] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) 2

theorem nb076_distinct_091 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy098 g a b) ≠ (nb076AlphaDummy099 g a b) := by
  simpa only [nb076AlphaDummy098, nb076AlphaDummy099] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_distinct_092 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy098 g a b) ≠ (nb076AlphaDummy100 g a b) := by
  simpa only [nb076AlphaDummy098, nb076AlphaDummy100] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb076_distinct_093 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy099 g a b) ≠ (nb076AlphaDummy100 g a b) := by
  simpa only [nb076AlphaDummy099, nb076AlphaDummy100] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb076_fresh_094 :
    (nb076AlphaDummy107) ∉
      (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy096))).fv) :=
  by
  simpa only [nb076AlphaDummy107] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy096))).fv)
      0

theorem nb076_fresh_095 :
    (nb076AlphaDummy103) ∉
      (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv) :=
  by
  simpa only [nb076AlphaDummy103] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv)
      0

theorem nb076_fresh_096 :
    (nb076AlphaDummy109) ∉
      (((Class.cv (nb076AlphaDummy097))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv) :=
  by
  simpa only [nb076AlphaDummy109] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy097))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv)
      0

theorem nb076_fresh_097 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy108 g a b) ∉
      (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy099 g a b))).fv) :=
  by
  simpa only [nb076AlphaDummy108] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy099 g a b))).fv)
      0

theorem nb076_fresh_098 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy104 g a b) ∉
      (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy100 g a b))).fv) :=
  by
  simpa only [nb076AlphaDummy104] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy100 g a b))).fv)
      0

theorem nb076_fresh_099 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy110 g a b) ∉
      (((Class.cv (nb076AlphaDummy100 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy100 g a b))).fv) :=
  by
  simpa only [nb076AlphaDummy110] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy100 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy100 g a b))).fv)
      0

theorem nb076_fresh_100 :
    (nb076AlphaDummy119) ∉
      (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv) :=
  by
  simpa only [nb076AlphaDummy119] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv)
      0

theorem nb076_fresh_101 :
    (nb076AlphaDummy120) ∉
      (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv) :=
  by
  simpa only [nb076AlphaDummy120] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv)
      1

theorem nb076_distinct_102 : (nb076AlphaDummy119) ≠ (nb076AlphaDummy120) := by
  simpa only [nb076AlphaDummy119, nb076AlphaDummy120] using
    (freshVar_injective
      (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_103 (g : Var) (b : Var) :
    (nb076AlphaDummy121 g b) ∉
      (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy116 g b))).fv) :=
  by
  simpa only [nb076AlphaDummy121] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy116 g b))).fv)
      0

theorem nb076_fresh_104 (g : Var) (b : Var) :
    (nb076AlphaDummy122 g b) ∉
      (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy116 g b))).fv) :=
  by
  simpa only [nb076AlphaDummy122] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy116 g b))).fv)
      1

theorem nb076_distinct_105 (g : Var) (b : Var) :
    (nb076AlphaDummy121 g b) ≠ (nb076AlphaDummy122 g b) := by
  simpa only [nb076AlphaDummy121, nb076AlphaDummy122] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy116 g b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_106 :
    (nb076AlphaDummy127) ∉ (((Class.cv (nb076AlphaDummy120))).fv) := by
  simpa only [nb076AlphaDummy127] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy120))).fv) 0

theorem nb076_fresh_107 :
    (nb076AlphaDummy128) ∉ (((Class.cv (nb076AlphaDummy120))).fv) := by
  simpa only [nb076AlphaDummy128] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy120))).fv) 1

theorem nb076_distinct_108 : (nb076AlphaDummy127) ≠ (nb076AlphaDummy128) := by
  simpa only [nb076AlphaDummy127, nb076AlphaDummy128] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy120))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_109 (g : Var) (b : Var) :
    (nb076AlphaDummy129 g b) ∉ (((Class.cv (nb076AlphaDummy122 g b))).fv) := by
  simpa only [nb076AlphaDummy129] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy122 g b))).fv) 0

theorem nb076_fresh_110 (g : Var) (b : Var) :
    (nb076AlphaDummy130 g b) ∉ (((Class.cv (nb076AlphaDummy122 g b))).fv) := by
  simpa only [nb076AlphaDummy130] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy122 g b))).fv) 1

theorem nb076_distinct_111 (g : Var) (b : Var) :
    (nb076AlphaDummy129 g b) ≠ (nb076AlphaDummy130 g b) := by
  simpa only [nb076AlphaDummy129, nb076AlphaDummy130] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy122 g b))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb076_fresh_112 :
    (nb076AlphaDummy133) ∉
      (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy133] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) 0

theorem nb076_fresh_113 :
    (nb076AlphaDummy134) ∉
      (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy134] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) 1

theorem nb076_fresh_114 :
    (nb076AlphaDummy135) ∉
      (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy135] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) 2

theorem nb076_distinct_115 : (nb076AlphaDummy133) ≠ (nb076AlphaDummy134) := by
  simpa only [nb076AlphaDummy133, nb076AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb076_distinct_116 : (nb076AlphaDummy133) ≠ (nb076AlphaDummy135) := by
  simpa only [nb076AlphaDummy133, nb076AlphaDummy135] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb076_distinct_117 : (nb076AlphaDummy134) ≠ (nb076AlphaDummy135) := by
  simpa only [nb076AlphaDummy134, nb076AlphaDummy135] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb076_fresh_118 (g : Var) (b : Var) :
    (nb076AlphaDummy136 g b) ∉
      (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy136] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) 0

theorem nb076_fresh_119 (g : Var) (b : Var) :
    (nb076AlphaDummy137 g b) ∉
      (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy137] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) 1

theorem nb076_fresh_120 (g : Var) (b : Var) :
    (nb076AlphaDummy138 g b) ∉
      (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb076AlphaDummy138] using
    freshVar_not_mem (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) 2

theorem nb076_distinct_121 (g : Var) (b : Var) :
    (nb076AlphaDummy136 g b) ≠ (nb076AlphaDummy137 g b) := by
  simpa only [nb076AlphaDummy136, nb076AlphaDummy137] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_distinct_122 (g : Var) (b : Var) :
    (nb076AlphaDummy136 g b) ≠ (nb076AlphaDummy138 g b) := by
  simpa only [nb076AlphaDummy136, nb076AlphaDummy138] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb076_distinct_123 (g : Var) (b : Var) :
    (nb076AlphaDummy137 g b) ≠ (nb076AlphaDummy138 g b) := by
  simpa only [nb076AlphaDummy137, nb076AlphaDummy138] using
    (freshVar_injective (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb076_fresh_124 :
    (nb076AlphaDummy145) ∉
      (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy134))).fv) :=
  by
  simpa only [nb076AlphaDummy145] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy134))).fv)
      0

theorem nb076_fresh_125 :
    (nb076AlphaDummy141) ∉
      (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv) :=
  by
  simpa only [nb076AlphaDummy141] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv)
      0

theorem nb076_fresh_126 :
    (nb076AlphaDummy147) ∉
      (((Class.cv (nb076AlphaDummy135))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv) :=
  by
  simpa only [nb076AlphaDummy147] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy135))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv)
      0

theorem nb076_fresh_127 (g : Var) (b : Var) :
    (nb076AlphaDummy146 g b) ∉
      (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy137 g b))).fv) :=
  by
  simpa only [nb076AlphaDummy146] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy137 g b))).fv)
      0

theorem nb076_fresh_128 (g : Var) (b : Var) :
    (nb076AlphaDummy142 g b) ∉
      (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy138 g b))).fv) :=
  by
  simpa only [nb076AlphaDummy142] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy138 g b))).fv)
      0

theorem nb076_fresh_129 (g : Var) (b : Var) :
    (nb076AlphaDummy148 g b) ∉
      (((Class.cv (nb076AlphaDummy138 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy138 g b))).fv) :=
  by
  simpa only [nb076AlphaDummy148] using
    freshVar_not_mem
      (((Class.cv (nb076AlphaDummy138 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy138 g b))).fv)
      0

theorem nb076_fresh_130 (g : Var) (b : Var) :
    (nb076AlphaDummy115 g b) ∉ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) := by
  simpa only [nb076AlphaDummy115] using
    freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 0

theorem nb076_fresh_131 (g : Var) (b : Var) :
    (nb076AlphaDummy116 g b) ∉ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) := by
  simpa only [nb076AlphaDummy116] using
    freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 1

theorem nb076_distinct_132 (g : Var) (b : Var) :
    (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy116 g b) := by
  simpa only [nb076AlphaDummy115, nb076AlphaDummy116] using
    (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv g)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_133 (m : Var) (n : Var) :
    (nb076AlphaDummy019 m n) ∉ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) := by
  simpa only [nb076AlphaDummy019] using
    freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 0

theorem nb076_fresh_134 (m : Var) (n : Var) :
    (nb076AlphaDummy020 m n) ∉ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) := by
  simpa only [nb076AlphaDummy020] using
    freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 1

theorem nb076_distinct_135 (m : Var) (n : Var) :
    (nb076AlphaDummy019 m n) ≠ (nb076AlphaDummy020 m n) := by
  simpa only [nb076AlphaDummy019, nb076AlphaDummy020] using
    (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_136 :
    (nb076AlphaDummy029) ∉
      (((Wff.classMem (Class.cv (nb076AlphaDummy025)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy025)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy025))).fv) :=
  by
  simpa only [nb076AlphaDummy029] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076AlphaDummy025)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy025)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy025))).fv)
      0

theorem nb076_fresh_137 (m : Var) (n : Var) :
    (nb076AlphaDummy030 m n) ∉
      (((Wff.classMem (Class.cv (nb076AlphaDummy027 m n)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy027 m n)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy027 m n))).fv) :=
  by
  simpa only [nb076AlphaDummy030] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076AlphaDummy027 m n)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy027 m n)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy027 m n))).fv)
      0

theorem nb076_fresh_138 :
    (nb076AlphaDummy057) ∉
      (((Wff.classMem (Class.cv (nb076AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy053))).fv) :=
  by
  simpa only [nb076AlphaDummy057] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy053))).fv)
      0

theorem nb076_fresh_139 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy058 g m n a b) ∉
      (((Wff.classMem (Class.cv (nb076AlphaDummy055 g m n a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy055 g m n a b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy055 g m n a b))).fv) :=
  by
  simpa only [nb076AlphaDummy058] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076AlphaDummy055 g m n a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy055 g m n a b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy055 g m n a b))).fv)
      0

theorem nb076_fresh_140 :
    (nb076AlphaDummy093) ∉
      (((Wff.classMem (Class.cv (nb076AlphaDummy089)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy089)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy089))).fv) :=
  by
  simpa only [nb076AlphaDummy093] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076AlphaDummy089)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy089)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy089))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part003`. -/


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

theorem nb076_fresh_141 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy094 g a b) ∉
      (((Wff.classMem (Class.cv (nb076AlphaDummy091 g a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy091 g a b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy091 g a b))).fv) :=
  by
  simpa only [nb076AlphaDummy094] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076AlphaDummy091 g a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy091 g a b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy091 g a b))).fv)
      0

theorem nb076_fresh_142 :
    (nb076AlphaDummy131) ∉
      (((Wff.classMem (Class.cv (nb076AlphaDummy127)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy127)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy127))).fv) :=
  by
  simpa only [nb076AlphaDummy131] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076AlphaDummy127)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy127)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy127))).fv)
      0

theorem nb076_fresh_143 (g : Var) (b : Var) :
    (nb076AlphaDummy132 g b) ∉
      (((Wff.classMem (Class.cv (nb076AlphaDummy129 g b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy129 g b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy129 g b))).fv) :=
  by
  simpa only [nb076AlphaDummy132] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076AlphaDummy129 g b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy129 g b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy129 g b))).fv)
      0

theorem nb076_fresh_144 :
    (nb076AlphaDummy013) ∉
      (((synCcompl (Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
                (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCphi (Class.cv (nb076AlphaDummy010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy009)
              (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy013] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
                (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCphi (Class.cv (nb076AlphaDummy010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy009)
              (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb076_fresh_145 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy014 g m n a b) ∉
      (((synCcompl (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b)
                (Class.cv (nb076AlphaDummy006 g m n a b))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy014] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b)
                (Class.cv (nb076AlphaDummy006 g m n a b))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb076_fresh_146 :
    (nb076AlphaDummy021) ∉
      (((synCcompl (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCphi (Class.cv (nb076AlphaDummy018)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy021] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCphi (Class.cv (nb076AlphaDummy018)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb076_fresh_147 (m : Var) (n : Var) :
    (nb076AlphaDummy022 m n) ∉
      (((synCcompl (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCphi (Class.cv (nb076AlphaDummy020 m n)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy022] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCphi (Class.cv (nb076AlphaDummy020 m n)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb076_fresh_148 :
    (nb076AlphaDummy085) ∉
      (((synCcompl (Class.cab (nb076AlphaDummy081)
              (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCphi (Class.cv (nb076AlphaDummy082)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
                (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy085] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb076AlphaDummy081)
              (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCphi (Class.cv (nb076AlphaDummy082)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
                (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb076_fresh_149 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy086 g a b) ∉
      (((synCcompl (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCphi (Class.cv (nb076AlphaDummy084 g a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy086] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCphi (Class.cv (nb076AlphaDummy084 g a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb076_fresh_150 :
    (nb076AlphaDummy123) ∉
      (((synCcompl (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCphi (Class.cv (nb076AlphaDummy120)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy123] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCphi (Class.cv (nb076AlphaDummy120)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb076_fresh_151 (g : Var) (b : Var) :
    (nb076AlphaDummy124 g b) ∉
      (((synCcompl (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCphi (Class.cv (nb076AlphaDummy122 g b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy124] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCphi (Class.cv (nb076AlphaDummy122 g b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb076_fresh_152 :
    (nb076AlphaDummy041) ∉
      (((synCcompl (Class.cv (nb076AlphaDummy032)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy033)))).fv) :=
  by
  simpa only [nb076AlphaDummy041] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb076AlphaDummy032)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy033)))).fv)
      0

theorem nb076_fresh_153 (m : Var) (n : Var) :
    (nb076AlphaDummy042 m n) ∉
      (((synCcompl (Class.cv (nb076AlphaDummy035 m n)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy036 m n)))).fv) :=
  by
  simpa only [nb076AlphaDummy042] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb076AlphaDummy035 m n)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy036 m n)))).fv)
      0

theorem nb076_fresh_154 :
    (nb076AlphaDummy069) ∉
      (((synCcompl (Class.cv (nb076AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy061)))).fv) :=
  by
  simpa only [nb076AlphaDummy069] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb076AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy061)))).fv)
      0

theorem nb076_fresh_155 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy070 g m n a b) ∉
      (((synCcompl (Class.cv (nb076AlphaDummy063 g m n a b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy064 g m n a b)))).fv) :=
  by
  simpa only [nb076AlphaDummy070] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb076AlphaDummy063 g m n a b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy064 g m n a b)))).fv)
      0

theorem nb076_fresh_156 :
    (nb076AlphaDummy105) ∉
      (((synCcompl (Class.cv (nb076AlphaDummy096)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy097)))).fv) :=
  by
  simpa only [nb076AlphaDummy105] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb076AlphaDummy096)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy097)))).fv)
      0

theorem nb076_fresh_157 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy106 g a b) ∉
      (((synCcompl (Class.cv (nb076AlphaDummy099 g a b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy100 g a b)))).fv) :=
  by
  simpa only [nb076AlphaDummy106] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb076AlphaDummy099 g a b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy100 g a b)))).fv)
      0

theorem nb076_fresh_158 :
    (nb076AlphaDummy143) ∉
      (((synCcompl (Class.cv (nb076AlphaDummy134)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy135)))).fv) :=
  by
  simpa only [nb076AlphaDummy143] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb076AlphaDummy134)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy135)))).fv)
      0

theorem nb076_fresh_159 (g : Var) (b : Var) :
    (nb076AlphaDummy144 g b) ∉
      (((synCcompl (Class.cv (nb076AlphaDummy137 g b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy138 g b)))).fv) :=
  by
  simpa only [nb076AlphaDummy144] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb076AlphaDummy137 g b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy138 g b)))).fv)
      0

theorem nb076_fresh_160 :
    (nb076AlphaDummy077) ∉
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy010))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb076AlphaDummy077] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy010))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb076_fresh_161 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy078 g m n a b) ∉
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb076AlphaDummy078] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb076_fresh_162 :
    (nb076AlphaDummy049) ∉
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy018))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb076AlphaDummy049] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy018))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb076_fresh_163 (m : Var) (n : Var) :
    (nb076AlphaDummy050 m n) ∉
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy020 m n))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb076AlphaDummy050] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy020 m n))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb076_fresh_164 :
    (nb076AlphaDummy155) ∉
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy082))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb076AlphaDummy155] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy082))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb076_fresh_165 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy156 g a b) ∉
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy084 g a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb076AlphaDummy156] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy084 g a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb076_fresh_166 :
    (nb076AlphaDummy151) ∉
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy120))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb076AlphaDummy151] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy120))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb076_fresh_167 (g : Var) (b : Var) :
    (nb076AlphaDummy152 g b) ∉
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy122 g b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb076AlphaDummy152] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy122 g b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb076_fresh_168 :
    (nb076AlphaDummy037) ∉
      (((synCnin (Class.cv (nb076AlphaDummy032)) (Class.cv (nb076AlphaDummy033)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy032))
            (Class.cv (nb076AlphaDummy033)))).fv) :=
  by
  simpa only [nb076AlphaDummy037] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb076AlphaDummy032)) (Class.cv (nb076AlphaDummy033)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy032)) (Class.cv (nb076AlphaDummy033)))).fv)
      0

theorem nb076_fresh_169 (m : Var) (n : Var) :
    (nb076AlphaDummy038 m n) ∉
      (((synCnin (Class.cv (nb076AlphaDummy035 m n))
            (Class.cv (nb076AlphaDummy036 m n)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy035 m n))
            (Class.cv (nb076AlphaDummy036 m n)))).fv) :=
  by
  simpa only [nb076AlphaDummy038] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb076AlphaDummy035 m n))
            (Class.cv (nb076AlphaDummy036 m n)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy035 m n))
            (Class.cv (nb076AlphaDummy036 m n)))).fv)
      0

theorem nb076_fresh_170 :
    (nb076AlphaDummy065) ∉
      (((synCnin (Class.cv (nb076AlphaDummy060)) (Class.cv (nb076AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy060))
            (Class.cv (nb076AlphaDummy061)))).fv) :=
  by
  simpa only [nb076AlphaDummy065] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb076AlphaDummy060)) (Class.cv (nb076AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy060)) (Class.cv (nb076AlphaDummy061)))).fv)
      0

theorem nb076_fresh_171 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy066 g m n a b) ∉
      (((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
            (Class.cv (nb076AlphaDummy064 g m n a b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
            (Class.cv (nb076AlphaDummy064 g m n a b)))).fv) :=
  by
  simpa only [nb076AlphaDummy066] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
            (Class.cv (nb076AlphaDummy064 g m n a b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
            (Class.cv (nb076AlphaDummy064 g m n a b)))).fv)
      0

theorem nb076_fresh_172 :
    (nb076AlphaDummy101) ∉
      (((synCnin (Class.cv (nb076AlphaDummy096)) (Class.cv (nb076AlphaDummy097)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy096))
            (Class.cv (nb076AlphaDummy097)))).fv) :=
  by
  simpa only [nb076AlphaDummy101] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb076AlphaDummy096)) (Class.cv (nb076AlphaDummy097)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy096)) (Class.cv (nb076AlphaDummy097)))).fv)
      0

theorem nb076_fresh_173 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy102 g a b) ∉
      (((synCnin (Class.cv (nb076AlphaDummy099 g a b))
            (Class.cv (nb076AlphaDummy100 g a b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy099 g a b))
            (Class.cv (nb076AlphaDummy100 g a b)))).fv) :=
  by
  simpa only [nb076AlphaDummy102] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb076AlphaDummy099 g a b))
            (Class.cv (nb076AlphaDummy100 g a b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy099 g a b))
            (Class.cv (nb076AlphaDummy100 g a b)))).fv)
      0

theorem nb076_fresh_174 :
    (nb076AlphaDummy139) ∉
      (((synCnin (Class.cv (nb076AlphaDummy134)) (Class.cv (nb076AlphaDummy135)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy134))
            (Class.cv (nb076AlphaDummy135)))).fv) :=
  by
  simpa only [nb076AlphaDummy139] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb076AlphaDummy134)) (Class.cv (nb076AlphaDummy135)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy134)) (Class.cv (nb076AlphaDummy135)))).fv)
      0

theorem nb076_fresh_175 (g : Var) (b : Var) :
    (nb076AlphaDummy140 g b) ∉
      (((synCnin (Class.cv (nb076AlphaDummy137 g b))
            (Class.cv (nb076AlphaDummy138 g b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy137 g b))
            (Class.cv (nb076AlphaDummy138 g b)))).fv) :=
  by
  simpa only [nb076AlphaDummy140] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb076AlphaDummy137 g b))
            (Class.cv (nb076AlphaDummy138 g b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy137 g b))
            (Class.cv (nb076AlphaDummy138 g b)))).fv)
      0

theorem nb076_fresh_176 :
    (nb076AlphaDummy009) ∉
      (((synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))).fv ∪
        ((Class.cv (nb076AlphaDummy005))).fv) :=
  by
  simpa only [nb076AlphaDummy009] using
    freshVar_not_mem
      (((synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))).fv ∪
        ((Class.cv (nb076AlphaDummy005))).fv)
      0

theorem nb076_fresh_177 :
    (nb076AlphaDummy010) ∉
      (((synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))).fv ∪
        ((Class.cv (nb076AlphaDummy005))).fv) :=
  by
  simpa only [nb076AlphaDummy010] using
    freshVar_not_mem
      (((synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))).fv ∪
        ((Class.cv (nb076AlphaDummy005))).fv)
      1

theorem nb076_distinct_178 : (nb076AlphaDummy009) ≠ (nb076AlphaDummy010) := by
  simpa only [nb076AlphaDummy009, nb076AlphaDummy010] using
    (freshVar_injective (((synCop (Class.cv (nb076AlphaDummy003))
            (Class.cv (nb076AlphaDummy004)))).fv ∪ ((Class.cv (nb076AlphaDummy005))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_179 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy011 g m n a b) ∉
      (((synCop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) :=
  by
  simpa only [nb076AlphaDummy011] using
    freshVar_not_mem
      (((synCop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv)
      0

theorem nb076_fresh_180 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy012 g m n a b) ∉
      (((synCop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) :=
  by
  simpa only [nb076AlphaDummy012] using
    freshVar_not_mem
      (((synCop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv)
      1

theorem nb076_distinct_181 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy011 g m n a b) ≠ (nb076AlphaDummy012 g m n a b) := by
  simpa only [nb076AlphaDummy011, nb076AlphaDummy012] using
    (freshVar_injective (((synCop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_182 :
    (nb076AlphaDummy079) ∉
      (((synCphi (Class.cv (nb076AlphaDummy010)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy010)))).fv) :=
  by
  simpa only [nb076AlphaDummy079] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb076AlphaDummy010)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy010)))).fv)
      0

theorem nb076_fresh_183 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy080 g m n a b) ∉
      (((synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))).fv) :=
  by
  simpa only [nb076AlphaDummy080] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))).fv)
      0

theorem nb076_fresh_184 :
    (nb076AlphaDummy051) ∉
      (((synCphi (Class.cv (nb076AlphaDummy018)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy018)))).fv) :=
  by
  simpa only [nb076AlphaDummy051] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb076AlphaDummy018)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy018)))).fv)
      0

theorem nb076_fresh_185 (m : Var) (n : Var) :
    (nb076AlphaDummy052 m n) ∉
      (((synCphi (Class.cv (nb076AlphaDummy020 m n)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy020 m n)))).fv) :=
  by
  simpa only [nb076AlphaDummy052] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb076AlphaDummy020 m n)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy020 m n)))).fv)
      0

theorem nb076_fresh_186 :
    (nb076AlphaDummy157) ∉
      (((synCphi (Class.cv (nb076AlphaDummy082)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy082)))).fv) :=
  by
  simpa only [nb076AlphaDummy157] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb076AlphaDummy082)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy082)))).fv)
      0

theorem nb076_fresh_187 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy158 g a b) ∉
      (((synCphi (Class.cv (nb076AlphaDummy084 g a b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy084 g a b)))).fv) :=
  by
  simpa only [nb076AlphaDummy158] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb076AlphaDummy084 g a b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy084 g a b)))).fv)
      0

theorem nb076_fresh_188 :
    (nb076AlphaDummy153) ∉
      (((synCphi (Class.cv (nb076AlphaDummy120)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy120)))).fv) :=
  by
  simpa only [nb076AlphaDummy153] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb076AlphaDummy120)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy120)))).fv)
      0

theorem nb076_fresh_189 (g : Var) (b : Var) :
    (nb076AlphaDummy154 g b) ∉
      (((synCphi (Class.cv (nb076AlphaDummy122 g b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy122 g b)))).fv) :=
  by
  simpa only [nb076AlphaDummy154] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb076AlphaDummy122 g b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy122 g b)))).fv)
      0

theorem nb076_fresh_190 :
    (nb076AlphaDummy005) ∉
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ((synCncs)).fv ∪
            ({(nb076AlphaDummy004)} : Finset Var) ∪ ((synCncs)).fv ∪
        ((Class.cab (nb076AlphaDummy000)
            (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
              (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                  (synCxp (Class.cv (nb076AlphaDummy001))
                    (Class.cv (nb076AlphaDummy002)))))))).fv) :=
  by
  simpa only [nb076AlphaDummy005] using
    freshVar_not_mem
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ((synCncs)).fv ∪
            ({(nb076AlphaDummy004)} : Finset Var) ∪ ((synCncs)).fv ∪
        ((Class.cab (nb076AlphaDummy000)
            (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
              (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                  (synCxp (Class.cv (nb076AlphaDummy001))
                    (Class.cv (nb076AlphaDummy002)))))))).fv)
      0

theorem nb076_fresh_191 :
    (nb076AlphaDummy007) ∉
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ({(nb076AlphaDummy004)} : Finset Var) ∪
          ({(nb076AlphaDummy005)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb076AlphaDummy003)) (synCncs))
              (Wff.classMem (Class.cv (nb076AlphaDummy004)) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy005)) (Class.cab (nb076AlphaDummy000)
                (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
                  (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                    (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                      (synCxp (Class.cv (nb076AlphaDummy001))
                        (Class.cv (nb076AlphaDummy002)))))))))).fv) :=
  by
  simpa only [nb076AlphaDummy007] using
    freshVar_not_mem
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ({(nb076AlphaDummy004)} : Finset Var) ∪
          ({(nb076AlphaDummy005)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb076AlphaDummy003)) (synCncs))
              (Wff.classMem (Class.cv (nb076AlphaDummy004)) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy005)) (Class.cab (nb076AlphaDummy000)
                (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
                  (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                    (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                      (synCxp (Class.cv (nb076AlphaDummy001))
                        (Class.cv (nb076AlphaDummy002)))))))))).fv)
      0

theorem nb076_fresh_192 :
    (nb076AlphaDummy117) ∉
      (({(nb076AlphaDummy113)} : Finset Var) ∪ ({(nb076AlphaDummy114)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy113))
              (Class.cv (nb076AlphaDummy001)))
            (Wff.classMem (Class.cv (nb076AlphaDummy114))
              (Class.cv (nb076AlphaDummy002))))).fv) :=
  by
  simpa only [nb076AlphaDummy117] using
    freshVar_not_mem
      (({(nb076AlphaDummy113)} : Finset Var) ∪ ({(nb076AlphaDummy114)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy113))
              (Class.cv (nb076AlphaDummy001)))
            (Wff.classMem (Class.cv (nb076AlphaDummy114))
              (Class.cv (nb076AlphaDummy002))))).fv)
      0

theorem nb076_fresh_193 (g : Var) (b : Var) :
    (nb076AlphaDummy118 g b) ∉
      (({(nb076AlphaDummy115 g b)} : Finset Var) ∪
          ({(nb076AlphaDummy116 g b)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076AlphaDummy116 g b)) (Class.cv g)))).fv) :=
  by
  simpa only [nb076AlphaDummy118] using
    freshVar_not_mem
      (({(nb076AlphaDummy115 g b)} : Finset Var) ∪
          ({(nb076AlphaDummy116 g b)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076AlphaDummy116 g b)) (Class.cv g)))).fv)
      0

theorem nb076_fresh_194 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy006 g m n a b) ∉
      (({ m } : Finset Var) ∪ ((synCncs)).fv ∪ ({ n } : Finset Var) ∪ ((synCncs)).fv ∪
        ((Class.cab a (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                (synWbr (Class.cv a) (synCen) (synCxp (Class.cv b) (Class.cv g))))))).fv) :=
  by
  simpa only [nb076AlphaDummy006] using
    freshVar_not_mem
      (({ m } : Finset Var) ∪ ((synCncs)).fv ∪ ({ n } : Finset Var) ∪ ((synCncs)).fv ∪
        ((Class.cab a (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                (synWbr (Class.cv a) (synCen) (synCxp (Class.cv b) (Class.cv g))))))).fv)
      0

theorem nb076_fresh_195 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy008 g m n a b) ∉
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076AlphaDummy006 g m n a b)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv m) (synCncs))
              (Wff.classMem (Class.cv n) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy006 g m n a b)) (Class.cab a
                (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                    (synWbr (Class.cv a) (synCen)
                      (synCxp (Class.cv b) (Class.cv g))))))))).fv) :=
  by
  simpa only [nb076AlphaDummy008] using
    freshVar_not_mem
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076AlphaDummy006 g m n a b)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv m) (synCncs))
              (Wff.classMem (Class.cv n) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy006 g m n a b)) (Class.cab a
                (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                    (synWbr (Class.cv a) (synCen)
                      (synCxp (Class.cv b) (Class.cv g))))))))).fv)
      0

theorem nb076_fresh_196 : (nb076AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb076_fresh_197 : (nb076AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb076_fresh_198 : (nb076AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb076_fresh_199 : (nb076AlphaDummy003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076AlphaDummy003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb076_fresh_200 : (nb076AlphaDummy004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076AlphaDummy004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb076_distinct_201 : (nb076AlphaDummy000) ≠ (nb076AlphaDummy001) := by
  simpa only [nb076AlphaDummy000, nb076AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_202 : (nb076AlphaDummy000) ≠ (nb076AlphaDummy002) := by
  simpa only [nb076AlphaDummy000, nb076AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_203 : (nb076AlphaDummy000) ≠ (nb076AlphaDummy003) := by
  simpa only [nb076AlphaDummy000, nb076AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb076_distinct_204 : (nb076AlphaDummy000) ≠ (nb076AlphaDummy004) := by
  simpa only [nb076AlphaDummy000, nb076AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb076_distinct_205 : (nb076AlphaDummy001) ≠ (nb076AlphaDummy002) := by
  simpa only [nb076AlphaDummy001, nb076AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb076_distinct_206 : (nb076AlphaDummy001) ≠ (nb076AlphaDummy003) := by
  simpa only [nb076AlphaDummy001, nb076AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb076_distinct_207 : (nb076AlphaDummy001) ≠ (nb076AlphaDummy004) := by
  simpa only [nb076AlphaDummy001, nb076AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb076_distinct_208 : (nb076AlphaDummy002) ≠ (nb076AlphaDummy003) := by
  simpa only [nb076AlphaDummy002, nb076AlphaDummy003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb076_distinct_209 : (nb076AlphaDummy002) ≠ (nb076AlphaDummy004) := by
  simpa only [nb076AlphaDummy002, nb076AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb076_distinct_210 : (nb076AlphaDummy003) ≠ (nb076AlphaDummy004) := by
  simpa only [nb076AlphaDummy003, nb076AlphaDummy004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb076_support_mem_0000 :
    (nb076AlphaDummy003) ∈
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ({(nb076AlphaDummy004)} : Finset Var) ∪
          ({(nb076AlphaDummy005)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb076AlphaDummy003)) (synCncs))
              (Wff.classMem (Class.cv (nb076AlphaDummy004)) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy005)) (Class.cab (nb076AlphaDummy000)
                (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
                  (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                    (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                      (synCxp (Class.cv (nb076AlphaDummy001))
                        (Class.cv (nb076AlphaDummy002)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0001 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076AlphaDummy006 g m n a b)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv m) (synCncs))
              (Wff.classMem (Class.cv n) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy006 g m n a b)) (Class.cab a
                (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                    (synWbr (Class.cv a) (synCen)
                      (synCxp (Class.cv b) (Class.cv g))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0002 :
    (nb076AlphaDummy004) ∈
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ({(nb076AlphaDummy004)} : Finset Var) ∪
          ({(nb076AlphaDummy005)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb076AlphaDummy003)) (synCncs))
              (Wff.classMem (Class.cv (nb076AlphaDummy004)) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy005)) (Class.cab (nb076AlphaDummy000)
                (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
                  (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                    (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                      (synCxp (Class.cv (nb076AlphaDummy001))
                        (Class.cv (nb076AlphaDummy002)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0003 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076AlphaDummy006 g m n a b)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv m) (synCncs))
              (Wff.classMem (Class.cv n) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy006 g m n a b)) (Class.cab a
                (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                    (synWbr (Class.cv a) (synCen)
                      (synCxp (Class.cv b) (Class.cv g))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0004 :
    (nb076AlphaDummy005) ∈
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ({(nb076AlphaDummy004)} : Finset Var) ∪
          ({(nb076AlphaDummy005)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb076AlphaDummy003)) (synCncs))
              (Wff.classMem (Class.cv (nb076AlphaDummy004)) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy005)) (Class.cab (nb076AlphaDummy000)
                (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
                  (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                    (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                      (synCxp (Class.cv (nb076AlphaDummy001))
                        (Class.cv (nb076AlphaDummy002)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0005 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy006 g m n a b) ∈
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076AlphaDummy006 g m n a b)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv m) (synCncs))
              (Wff.classMem (Class.cv n) (synCncs)))
            (Wff.classEq (Class.cv (nb076AlphaDummy006 g m n a b)) (Class.cab a
                (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                    (synWbr (Class.cv a) (synCen)
                      (synCxp (Class.cv b) (Class.cv g))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0006 :
    (nb076AlphaDummy003) ∈
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ((synCncs)).fv ∪
            ({(nb076AlphaDummy004)} : Finset Var) ∪ ((synCncs)).fv ∪
        ((Class.cab (nb076AlphaDummy000)
            (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
              (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                  (synCxp (Class.cv (nb076AlphaDummy001))
                    (Class.cv (nb076AlphaDummy002)))))))).fv) :=
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

theorem nb076_support_mem_0007 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (({ m } : Finset Var) ∪ ((synCncs)).fv ∪ ({ n } : Finset Var) ∪ ((synCncs)).fv ∪
        ((Class.cab a (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                (synWbr (Class.cv a) (synCen) (synCxp (Class.cv b) (Class.cv g))))))).fv) :=
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

theorem nb076_support_mem_0008 :
    (nb076AlphaDummy003) ∈
      (((synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))).fv ∪
        ((Class.cv (nb076AlphaDummy005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0009 :
    (nb076AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
                (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCphi (Class.cv (nb076AlphaDummy010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy009)
              (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy009) from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy010) from (by
            unfold nb076AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0010 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (((synCop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0011 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (((synCcompl (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b)
                (Class.cv (nb076AlphaDummy006 g m n a b))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb076AlphaDummy012 g m n a b) from (by
            unfold nb076AlphaDummy012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0012 :
    (nb076AlphaDummy003) ∈
      (((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))).fv ∪
        ((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy009) from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy010) from (by
            unfold nb076AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0013 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (((Class.cab (nb076AlphaDummy011 g m n a b) (synWrex (nb076AlphaDummy012 g m n a b)
              (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb076AlphaDummy012 g m n a b) from (by
            unfold nb076AlphaDummy012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0014 :
    (nb076AlphaDummy003) ∈
      (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0015 :
    (nb076AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCphi (Class.cv (nb076AlphaDummy018)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy017) from (by
          unfold nb076AlphaDummy017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy018) from (by
            unfold nb076AlphaDummy018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0016 (m : Var) (n : Var) :
    m ∈ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0017 (m : Var) (n : Var) :
    m ∈
      (((synCcompl (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCphi (Class.cv (nb076AlphaDummy020 m n)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb076AlphaDummy019 m n) from (by
          unfold nb076AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb076AlphaDummy020 m n) from (by
            unfold nb076AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0018 :
    (nb076AlphaDummy003) ∈
      (((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCphi (Class.cv (nb076AlphaDummy018))))))).fv ∪
        ((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCphi (Class.cv (nb076AlphaDummy018))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy017) from (by
          unfold nb076AlphaDummy017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy018) from (by
            unfold nb076AlphaDummy018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0019 (m : Var) (n : Var) :
    m ∈
      (((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCphi (Class.cv (nb076AlphaDummy020 m n))))))).fv ∪
        ((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCphi (Class.cv (nb076AlphaDummy020 m n))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb076AlphaDummy019 m n) from (by
          unfold nb076AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb076AlphaDummy020 m n) from (by
            unfold nb076AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0020 :
    (nb076AlphaDummy018) ∈ (((Class.cv (nb076AlphaDummy018))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0021 (m : Var) (n : Var) :
    (nb076AlphaDummy020 m n) ∈ (((Class.cv (nb076AlphaDummy020 m n))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0022 :
    (nb076AlphaDummy025) ∈
      (((Wff.classMem (Class.cv (nb076AlphaDummy025)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy025)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy025))).fv) :=
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

theorem nb076_support_mem_0023 (m : Var) (n : Var) :
    (nb076AlphaDummy027 m n) ∈
      (((Wff.classMem (Class.cv (nb076AlphaDummy027 m n)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy027 m n)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy027 m n))).fv) :=
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

theorem nb076_support_mem_0024 :
    (nb076AlphaDummy025) ∈
      (((Class.cv (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0025 (m : Var) (n : Var) :
    (nb076AlphaDummy027 m n) ∈
      (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0026 :
    (nb076AlphaDummy032) ∈
      (((synCnin (Class.cv (nb076AlphaDummy032)) (Class.cv (nb076AlphaDummy033)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy032))
            (Class.cv (nb076AlphaDummy033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0027 (m : Var) (n : Var) :
    (nb076AlphaDummy035 m n) ∈
      (((synCnin (Class.cv (nb076AlphaDummy035 m n))
            (Class.cv (nb076AlphaDummy036 m n)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy035 m n))
            (Class.cv (nb076AlphaDummy036 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0028 :
    (nb076AlphaDummy032) ∈
      (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0029 (m : Var) (n : Var) :
    (nb076AlphaDummy035 m n) ∈
      (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy036 m n))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0030 :
    (nb076AlphaDummy033) ∈
      (((synCnin (Class.cv (nb076AlphaDummy032)) (Class.cv (nb076AlphaDummy033)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy032))
            (Class.cv (nb076AlphaDummy033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0031 (m : Var) (n : Var) :
    (nb076AlphaDummy036 m n) ∈
      (((synCnin (Class.cv (nb076AlphaDummy035 m n))
            (Class.cv (nb076AlphaDummy036 m n)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy035 m n))
            (Class.cv (nb076AlphaDummy036 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0032 :
    (nb076AlphaDummy033) ∈
      (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0033 (m : Var) (n : Var) :
    (nb076AlphaDummy036 m n) ∈
      (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy036 m n))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0034 :
    (nb076AlphaDummy032) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy032)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0035 (m : Var) (n : Var) :
    (nb076AlphaDummy035 m n) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy035 m n)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy036 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0036 :
    (nb076AlphaDummy032) ∈
      (((Class.cv (nb076AlphaDummy032))).fv ∪ ((Class.cv (nb076AlphaDummy032))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0037 (m : Var) (n : Var) :
    (nb076AlphaDummy035 m n) ∈
      (((Class.cv (nb076AlphaDummy035 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy035 m n))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0038 :
    (nb076AlphaDummy033) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy032)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0039 (m : Var) (n : Var) :
    (nb076AlphaDummy036 m n) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy035 m n)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy036 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0040 :
    (nb076AlphaDummy033) ∈
      (((Class.cv (nb076AlphaDummy033))).fv ∪ ((Class.cv (nb076AlphaDummy033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0041 (m : Var) (n : Var) :
    (nb076AlphaDummy036 m n) ∈
      (((Class.cv (nb076AlphaDummy036 m n))).fv ∪
        ((Class.cv (nb076AlphaDummy036 m n))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0042 :
    (nb076AlphaDummy004) ∈
      (({(nb076AlphaDummy003)} : Finset Var) ∪ ((synCncs)).fv ∪
            ({(nb076AlphaDummy004)} : Finset Var) ∪ ((synCncs)).fv ∪
        ((Class.cab (nb076AlphaDummy000)
            (synWrex (nb076AlphaDummy001) (Class.cv (nb076AlphaDummy003))
              (synWrex (nb076AlphaDummy002) (Class.cv (nb076AlphaDummy004))
                (synWbr (Class.cv (nb076AlphaDummy000)) (synCen)
                  (synCxp (Class.cv (nb076AlphaDummy001))
                    (Class.cv (nb076AlphaDummy002)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0043 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (({ m } : Finset Var) ∪ ((synCncs)).fv ∪ ({ n } : Finset Var) ∪ ((synCncs)).fv ∪
        ((Class.cab a (synWrex b (Class.cv m) (synWrex g (Class.cv n)
                (synWbr (Class.cv a) (synCen) (synCxp (Class.cv b) (Class.cv g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0044 :
    (nb076AlphaDummy004) ∈
      (((synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))).fv ∪
        ((Class.cv (nb076AlphaDummy005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0045 :
    (nb076AlphaDummy004) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
                (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCphi (Class.cv (nb076AlphaDummy010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy009)
              (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy009) from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy010) from (by
            unfold nb076AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0046 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (((synCop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0047 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (((synCcompl (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b)
                (Class.cv (nb076AlphaDummy006 g m n a b))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show n ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show n ≠ (nb076AlphaDummy012 g m n a b) from (by
            unfold nb076AlphaDummy012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part004`. -/


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

theorem nb076_support_mem_0048 :
    (nb076AlphaDummy004) ∈
      (((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))).fv ∪
        ((Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy009) from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy010) from (by
            unfold nb076AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0049 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (((Class.cab (nb076AlphaDummy011 g m n a b) (synWrex (nb076AlphaDummy012 g m n a b)
              (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show n ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show n ≠ (nb076AlphaDummy012 g m n a b) from (by
            unfold nb076AlphaDummy012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0050 :
    (nb076AlphaDummy004) ∈
      (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0051 :
    (nb076AlphaDummy004) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCphi (Class.cv (nb076AlphaDummy018)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy017) from (by
          unfold nb076AlphaDummy017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy018) from (by
            unfold nb076AlphaDummy018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0052 (m : Var) (n : Var) :
    n ∈ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0053 (m : Var) (n : Var) :
    n ∈
      (((synCcompl (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCphi (Class.cv (nb076AlphaDummy020 m n)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show n ≠ (nb076AlphaDummy019 m n) from (by
          unfold nb076AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show n ≠ (nb076AlphaDummy020 m n) from (by
            unfold nb076AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0054 :
    (nb076AlphaDummy004) ∈
      (((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy004))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCun (synCphi (Class.cv (nb076AlphaDummy018)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy017) from (by
          unfold nb076AlphaDummy017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy018) from (by
            unfold nb076AlphaDummy018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0055 (m : Var) (n : Var) :
    n ∈
      (((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCun (synCphi (Class.cv (nb076AlphaDummy020 m n)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show n ≠ (nb076AlphaDummy019 m n) from (by
          unfold nb076AlphaDummy019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show n ≠ (nb076AlphaDummy020 m n) from (by
            unfold nb076AlphaDummy020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0056 :
    (nb076AlphaDummy018) ∈
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy018))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0057 (m : Var) (n : Var) :
    (nb076AlphaDummy020 m n) ∈
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy020 m n))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0058 :
    (nb076AlphaDummy018) ∈
      (((synCphi (Class.cv (nb076AlphaDummy018)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy018)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0059 (m : Var) (n : Var) :
    (nb076AlphaDummy020 m n) ∈
      (((synCphi (Class.cv (nb076AlphaDummy020 m n)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy020 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0060 :
    (nb076AlphaDummy010) ∈ (((Class.cv (nb076AlphaDummy010))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0061 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy012 g m n a b) ∈
      (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0062 :
    (nb076AlphaDummy053) ∈
      (((Wff.classMem (Class.cv (nb076AlphaDummy053)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy053)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy053))).fv) :=
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

theorem nb076_support_mem_0063 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy055 g m n a b) ∈
      (((Wff.classMem (Class.cv (nb076AlphaDummy055 g m n a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy055 g m n a b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy055 g m n a b))).fv) :=
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

theorem nb076_support_mem_0064 :
    (nb076AlphaDummy053) ∈
      (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0065 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy055 g m n a b) ∈
      (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0066 :
    (nb076AlphaDummy060) ∈
      (((synCnin (Class.cv (nb076AlphaDummy060)) (Class.cv (nb076AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy060))
            (Class.cv (nb076AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0067 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy063 g m n a b) ∈
      (((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
            (Class.cv (nb076AlphaDummy064 g m n a b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
            (Class.cv (nb076AlphaDummy064 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0068 :
    (nb076AlphaDummy060) ∈
      (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0069 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy063 g m n a b) ∈
      (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy064 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0070 :
    (nb076AlphaDummy061) ∈
      (((synCnin (Class.cv (nb076AlphaDummy060)) (Class.cv (nb076AlphaDummy061)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy060))
            (Class.cv (nb076AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0071 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy064 g m n a b) ∈
      (((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
            (Class.cv (nb076AlphaDummy064 g m n a b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy063 g m n a b))
            (Class.cv (nb076AlphaDummy064 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0072 :
    (nb076AlphaDummy061) ∈
      (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0073 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy064 g m n a b) ∈
      (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy064 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0074 :
    (nb076AlphaDummy060) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0075 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy063 g m n a b) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy063 g m n a b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy064 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0076 :
    (nb076AlphaDummy060) ∈
      (((Class.cv (nb076AlphaDummy060))).fv ∪ ((Class.cv (nb076AlphaDummy060))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0077 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy063 g m n a b) ∈
      (((Class.cv (nb076AlphaDummy063 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy063 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0078 :
    (nb076AlphaDummy061) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy060)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0079 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy064 g m n a b) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy063 g m n a b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy064 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0080 :
    (nb076AlphaDummy061) ∈
      (((Class.cv (nb076AlphaDummy061))).fv ∪ ((Class.cv (nb076AlphaDummy061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0081 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy064 g m n a b) ∈
      (((Class.cv (nb076AlphaDummy064 g m n a b))).fv ∪
        ((Class.cv (nb076AlphaDummy064 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0082 :
    (nb076AlphaDummy005) ∈
      (((synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))).fv ∪
        ((Class.cv (nb076AlphaDummy005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0083 :
    (nb076AlphaDummy005) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
                (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCphi (Class.cv (nb076AlphaDummy010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy009)
              (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy009) from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy010) from (by
            unfold nb076AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0084 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy006 g m n a b) ∈
      (((synCop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0085 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy006 g m n a b) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b)
                (Class.cv (nb076AlphaDummy006 g m n a b))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy006 g m n a b) ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy006 g m n a b) ≠ (nb076AlphaDummy012 g m n a b) from (by
            unfold nb076AlphaDummy012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0086 :
    (nb076AlphaDummy005) ∈
      (((Class.cab (nb076AlphaDummy009)
            (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy009)
            (synWrex (nb076AlphaDummy010) (Class.cv (nb076AlphaDummy005))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCun (synCphi (Class.cv (nb076AlphaDummy010)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy009) from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy010) from (by
            unfold nb076AlphaDummy010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0087 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy006 g m n a b) ∈
      (((Class.cab (nb076AlphaDummy011 g m n a b) (synWrex (nb076AlphaDummy012 g m n a b)
              (Class.cv (nb076AlphaDummy006 g m n a b))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b)
              (Class.cv (nb076AlphaDummy006 g m n a b))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy006 g m n a b) ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy006 g m n a b) ≠ (nb076AlphaDummy012 g m n a b) from (by
            unfold nb076AlphaDummy012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0088 :
    (nb076AlphaDummy010) ∈
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy010))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0089 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy012 g m n a b) ∈
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0090 :
    (nb076AlphaDummy010) ∈
      (((synCphi (Class.cv (nb076AlphaDummy010)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy010)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0091 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy012 g m n a b) ∈
      (((synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0092 :
    (nb076AlphaDummy000) ∈
      (((Class.cv (nb076AlphaDummy000))).fv ∪ ((synCxp (Class.cv (nb076AlphaDummy001))
            (Class.cv (nb076AlphaDummy002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0093 :
    (nb076AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy081)
              (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCphi (Class.cv (nb076AlphaDummy082)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
                (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy081) from (by
          unfold nb076AlphaDummy081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy082) from (by
            unfold nb076AlphaDummy082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0094 (g : Var) (a : Var) (b : Var) :
    a ∈ (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0095 (g : Var) (a : Var) (b : Var) :
    a ∈
      (((synCcompl (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCphi (Class.cv (nb076AlphaDummy084 g a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb076AlphaDummy083 g a b) from (by
          unfold nb076AlphaDummy083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb076AlphaDummy084 g a b) from (by
            unfold nb076AlphaDummy084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0096 :
    (nb076AlphaDummy000) ∈
      (((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCphi (Class.cv (nb076AlphaDummy082))))))).fv ∪
        ((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCphi (Class.cv (nb076AlphaDummy082))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy081) from (by
          unfold nb076AlphaDummy081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy000) ≠ (nb076AlphaDummy082) from (by
            unfold nb076AlphaDummy082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0097 (g : Var) (a : Var) (b : Var) :
    a ∈
      (((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCphi (Class.cv (nb076AlphaDummy084 g a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb076AlphaDummy083 g a b) from (by
          unfold nb076AlphaDummy083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb076AlphaDummy084 g a b) from (by
            unfold nb076AlphaDummy084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0098 :
    (nb076AlphaDummy082) ∈ (((Class.cv (nb076AlphaDummy082))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0099 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy084 g a b) ∈ (((Class.cv (nb076AlphaDummy084 g a b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0100 :
    (nb076AlphaDummy089) ∈
      (((Wff.classMem (Class.cv (nb076AlphaDummy089)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy089)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy089))).fv) :=
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

theorem nb076_support_mem_0101 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy091 g a b) ∈
      (((Wff.classMem (Class.cv (nb076AlphaDummy091 g a b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy091 g a b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy091 g a b))).fv) :=
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

theorem nb076_support_mem_0102 :
    (nb076AlphaDummy089) ∈
      (((Class.cv (nb076AlphaDummy089))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0103 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy091 g a b) ∈
      (((Class.cv (nb076AlphaDummy091 g a b))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0104 :
    (nb076AlphaDummy096) ∈
      (((synCnin (Class.cv (nb076AlphaDummy096)) (Class.cv (nb076AlphaDummy097)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy096))
            (Class.cv (nb076AlphaDummy097)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0105 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy099 g a b) ∈
      (((synCnin (Class.cv (nb076AlphaDummy099 g a b))
            (Class.cv (nb076AlphaDummy100 g a b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy099 g a b))
            (Class.cv (nb076AlphaDummy100 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0106 :
    (nb076AlphaDummy096) ∈
      (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0107 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy099 g a b) ∈
      (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy100 g a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0108 :
    (nb076AlphaDummy097) ∈
      (((synCnin (Class.cv (nb076AlphaDummy096)) (Class.cv (nb076AlphaDummy097)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy096))
            (Class.cv (nb076AlphaDummy097)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0109 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy100 g a b) ∈
      (((synCnin (Class.cv (nb076AlphaDummy099 g a b))
            (Class.cv (nb076AlphaDummy100 g a b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy099 g a b))
            (Class.cv (nb076AlphaDummy100 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0110 :
    (nb076AlphaDummy097) ∈
      (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0111 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy100 g a b) ∈
      (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy100 g a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0112 :
    (nb076AlphaDummy096) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy096)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy097)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0113 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy099 g a b) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy099 g a b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy100 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0114 :
    (nb076AlphaDummy096) ∈
      (((Class.cv (nb076AlphaDummy096))).fv ∪ ((Class.cv (nb076AlphaDummy096))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0115 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy099 g a b) ∈
      (((Class.cv (nb076AlphaDummy099 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy099 g a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0116 :
    (nb076AlphaDummy097) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy096)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy097)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0117 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy100 g a b) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy099 g a b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy100 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0118 :
    (nb076AlphaDummy097) ∈
      (((Class.cv (nb076AlphaDummy097))).fv ∪ ((Class.cv (nb076AlphaDummy097))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0119 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy100 g a b) ∈
      (((Class.cv (nb076AlphaDummy100 g a b))).fv ∪
        ((Class.cv (nb076AlphaDummy100 g a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0120 :
    (nb076AlphaDummy113) ∈
      (({(nb076AlphaDummy113)} : Finset Var) ∪ ({(nb076AlphaDummy114)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy113))
              (Class.cv (nb076AlphaDummy001)))
            (Wff.classMem (Class.cv (nb076AlphaDummy114))
              (Class.cv (nb076AlphaDummy002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0121 (g : Var) (b : Var) :
    (nb076AlphaDummy115 g b) ∈
      (({(nb076AlphaDummy115 g b)} : Finset Var) ∪
          ({(nb076AlphaDummy116 g b)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076AlphaDummy116 g b)) (Class.cv g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0122 :
    (nb076AlphaDummy114) ∈
      (({(nb076AlphaDummy113)} : Finset Var) ∪ ({(nb076AlphaDummy114)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy113))
              (Class.cv (nb076AlphaDummy001)))
            (Wff.classMem (Class.cv (nb076AlphaDummy114))
              (Class.cv (nb076AlphaDummy002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0123 (g : Var) (b : Var) :
    (nb076AlphaDummy116 g b) ∈
      (({(nb076AlphaDummy115 g b)} : Finset Var) ∪
          ({(nb076AlphaDummy116 g b)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076AlphaDummy116 g b)) (Class.cv g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0124 :
    (nb076AlphaDummy113) ∈
      (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0125 :
    (nb076AlphaDummy113) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCphi (Class.cv (nb076AlphaDummy120)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy119) from (by
          unfold nb076AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy120) from (by
            unfold nb076AlphaDummy120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0126 (g : Var) (b : Var) :
    (nb076AlphaDummy115 g b) ∈
      (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy116 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0127 (g : Var) (b : Var) :
    (nb076AlphaDummy115 g b) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCphi (Class.cv (nb076AlphaDummy122 g b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy121 g b) from (by
          unfold nb076AlphaDummy121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy122 g b) from (by
            unfold nb076AlphaDummy122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0128 :
    (nb076AlphaDummy113) ∈
      (((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCphi (Class.cv (nb076AlphaDummy120))))))).fv ∪
        ((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCphi (Class.cv (nb076AlphaDummy120))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy119) from (by
          unfold nb076AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy113) ≠ (nb076AlphaDummy120) from (by
            unfold nb076AlphaDummy120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0129 (g : Var) (b : Var) :
    (nb076AlphaDummy115 g b) ∈
      (((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCphi (Class.cv (nb076AlphaDummy122 g b))))))).fv ∪
        ((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCphi (Class.cv (nb076AlphaDummy122 g b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy121 g b) from (by
          unfold nb076AlphaDummy121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy122 g b) from (by
            unfold nb076AlphaDummy122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0130 :
    (nb076AlphaDummy120) ∈ (((Class.cv (nb076AlphaDummy120))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0131 (g : Var) (b : Var) :
    (nb076AlphaDummy122 g b) ∈ (((Class.cv (nb076AlphaDummy122 g b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0132 :
    (nb076AlphaDummy127) ∈
      (((Wff.classMem (Class.cv (nb076AlphaDummy127)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy127)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy127))).fv) :=
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

theorem nb076_support_mem_0133 (g : Var) (b : Var) :
    (nb076AlphaDummy129 g b) ∈
      (((Wff.classMem (Class.cv (nb076AlphaDummy129 g b)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb076AlphaDummy129 g b)) (synC1c))).fv ∪
        ((Class.cv (nb076AlphaDummy129 g b))).fv) :=
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

theorem nb076_support_mem_0134 :
    (nb076AlphaDummy127) ∈
      (((Class.cv (nb076AlphaDummy127))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0135 (g : Var) (b : Var) :
    (nb076AlphaDummy129 g b) ∈
      (((Class.cv (nb076AlphaDummy129 g b))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0136 :
    (nb076AlphaDummy134) ∈
      (((synCnin (Class.cv (nb076AlphaDummy134)) (Class.cv (nb076AlphaDummy135)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy134))
            (Class.cv (nb076AlphaDummy135)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0137 (g : Var) (b : Var) :
    (nb076AlphaDummy137 g b) ∈
      (((synCnin (Class.cv (nb076AlphaDummy137 g b))
            (Class.cv (nb076AlphaDummy138 g b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy137 g b))
            (Class.cv (nb076AlphaDummy138 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0138 :
    (nb076AlphaDummy134) ∈
      (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0139 (g : Var) (b : Var) :
    (nb076AlphaDummy137 g b) ∈
      (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy138 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0140 :
    (nb076AlphaDummy135) ∈
      (((synCnin (Class.cv (nb076AlphaDummy134)) (Class.cv (nb076AlphaDummy135)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy134))
            (Class.cv (nb076AlphaDummy135)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0141 (g : Var) (b : Var) :
    (nb076AlphaDummy138 g b) ∈
      (((synCnin (Class.cv (nb076AlphaDummy137 g b))
            (Class.cv (nb076AlphaDummy138 g b)))).fv ∪
        ((synCnin (Class.cv (nb076AlphaDummy137 g b))
            (Class.cv (nb076AlphaDummy138 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0142 :
    (nb076AlphaDummy135) ∈
      (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0143 (g : Var) (b : Var) :
    (nb076AlphaDummy138 g b) ∈
      (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy138 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0144 :
    (nb076AlphaDummy134) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy134)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy135)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0145 (g : Var) (b : Var) :
    (nb076AlphaDummy137 g b) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy137 g b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy138 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0146 :
    (nb076AlphaDummy134) ∈
      (((Class.cv (nb076AlphaDummy134))).fv ∪ ((Class.cv (nb076AlphaDummy134))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0147 (g : Var) (b : Var) :
    (nb076AlphaDummy137 g b) ∈
      (((Class.cv (nb076AlphaDummy137 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy137 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0148 :
    (nb076AlphaDummy135) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy134)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy135)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0149 (g : Var) (b : Var) :
    (nb076AlphaDummy138 g b) ∈
      (((synCcompl (Class.cv (nb076AlphaDummy137 g b)))).fv ∪
        ((synCcompl (Class.cv (nb076AlphaDummy138 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0150 :
    (nb076AlphaDummy135) ∈
      (((Class.cv (nb076AlphaDummy135))).fv ∪ ((Class.cv (nb076AlphaDummy135))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0151 (g : Var) (b : Var) :
    (nb076AlphaDummy138 g b) ∈
      (((Class.cv (nb076AlphaDummy138 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy138 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0152 :
    (nb076AlphaDummy114) ∈
      (((Class.cv (nb076AlphaDummy113))).fv ∪ ((Class.cv (nb076AlphaDummy114))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0153 :
    (nb076AlphaDummy114) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy113))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCphi (Class.cv (nb076AlphaDummy120)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy119)
              (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
                (Wff.classEq (Class.cv (nb076AlphaDummy119))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy119) from (by
          unfold nb076AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy120) from (by
            unfold nb076AlphaDummy120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0154 (g : Var) (b : Var) :
    (nb076AlphaDummy116 g b) ∈
      (((Class.cv (nb076AlphaDummy115 g b))).fv ∪
        ((Class.cv (nb076AlphaDummy116 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0155 (g : Var) (b : Var) :
    (nb076AlphaDummy116 g b) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy115 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCphi (Class.cv (nb076AlphaDummy122 g b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy121 g b)
              (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
                (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy121 g b) from (by
          unfold nb076AlphaDummy121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy122 g b) from (by
            unfold nb076AlphaDummy122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0156 :
    (nb076AlphaDummy114) ∈
      (((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy119)
            (synWrex (nb076AlphaDummy120) (Class.cv (nb076AlphaDummy114))
              (Wff.classEq (Class.cv (nb076AlphaDummy119))
                (synCun (synCphi (Class.cv (nb076AlphaDummy120)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy119) from (by
          unfold nb076AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy120) from (by
            unfold nb076AlphaDummy120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0157 (g : Var) (b : Var) :
    (nb076AlphaDummy116 g b) ∈
      (((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy121 g b)
            (synWrex (nb076AlphaDummy122 g b) (Class.cv (nb076AlphaDummy116 g b))
              (Wff.classEq (Class.cv (nb076AlphaDummy121 g b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy122 g b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy121 g b) from (by
          unfold nb076AlphaDummy121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy122 g b) from (by
            unfold nb076AlphaDummy122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0158 :
    (nb076AlphaDummy120) ∈
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy120))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0159 (g : Var) (b : Var) :
    (nb076AlphaDummy122 g b) ∈
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy122 g b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0160 :
    (nb076AlphaDummy120) ∈
      (((synCphi (Class.cv (nb076AlphaDummy120)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy120)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0161 (g : Var) (b : Var) :
    (nb076AlphaDummy122 g b) ∈
      (((synCphi (Class.cv (nb076AlphaDummy122 g b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy122 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0162 :
    (nb076AlphaDummy001) ∈
      (((Class.cv (nb076AlphaDummy000))).fv ∪ ((synCxp (Class.cv (nb076AlphaDummy001))
            (Class.cv (nb076AlphaDummy002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0163 :
    (nb076AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy081)
              (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCphi (Class.cv (nb076AlphaDummy082)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
                (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy081) from (by
          unfold nb076AlphaDummy081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy082) from (by
            unfold nb076AlphaDummy082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0164 (g : Var) (a : Var) (b : Var) :
    b ∈ (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0165 (g : Var) (a : Var) (b : Var) :
    b ∈
      (((synCcompl (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCphi (Class.cv (nb076AlphaDummy084 g a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb076AlphaDummy083 g a b) from (by
          unfold nb076AlphaDummy083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb076AlphaDummy084 g a b) from (by
            unfold nb076AlphaDummy084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0166 :
    (nb076AlphaDummy001) ∈
      (((Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
              (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (synCxp (Class.cv (nb076AlphaDummy001))
                (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy081) from (by
          unfold nb076AlphaDummy081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy082) from (by
            unfold nb076AlphaDummy082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0167 (g : Var) (a : Var) (b : Var) :
    b ∈
      (((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb076AlphaDummy083 g a b) from (by
          unfold nb076AlphaDummy083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb076AlphaDummy084 g a b) from (by
            unfold nb076AlphaDummy084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0168 :
    (nb076AlphaDummy001) ∈
      (({(nb076AlphaDummy113)} : Finset Var) ∪ ({(nb076AlphaDummy114)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy113))
              (Class.cv (nb076AlphaDummy001)))
            (Wff.classMem (Class.cv (nb076AlphaDummy114))
              (Class.cv (nb076AlphaDummy002))))).fv) :=
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

theorem nb076_support_mem_0169 (g : Var) (b : Var) :
    b ∈
      (({(nb076AlphaDummy115 g b)} : Finset Var) ∪
          ({(nb076AlphaDummy116 g b)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076AlphaDummy116 g b)) (Class.cv g)))).fv) :=
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

theorem nb076_support_mem_0170 :
    (nb076AlphaDummy001) ∈
      (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0171 (g : Var) (b : Var) :
    b ∈ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0172 :
    (nb076AlphaDummy002) ∈
      (((Class.cv (nb076AlphaDummy000))).fv ∪ ((synCxp (Class.cv (nb076AlphaDummy001))
            (Class.cv (nb076AlphaDummy002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0173 :
    (nb076AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb076AlphaDummy081)
              (synWrex (nb076AlphaDummy082) (Class.cv (nb076AlphaDummy000))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCphi (Class.cv (nb076AlphaDummy082)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
                (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
                (Wff.classEq (Class.cv (nb076AlphaDummy081))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy081) from (by
          unfold nb076AlphaDummy081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy082) from (by
            unfold nb076AlphaDummy082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0174 (g : Var) (a : Var) (b : Var) :
    g ∈ (((Class.cv a)).fv ∪ ((synCxp (Class.cv b) (Class.cv g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0175 (g : Var) (a : Var) (b : Var) :
    g ∈
      (((synCcompl (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCphi (Class.cv (nb076AlphaDummy084 g a b)))))))).fv ∪ ((synCcompl
            (Class.cab (nb076AlphaDummy083 g a b)
              (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                  (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show g ≠ (nb076AlphaDummy083 g a b) from (by
          unfold nb076AlphaDummy083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show g ≠ (nb076AlphaDummy084 g a b) from (by
            unfold nb076AlphaDummy084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
