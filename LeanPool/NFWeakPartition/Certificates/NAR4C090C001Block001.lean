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

/-! Certificates from `NAR4C090C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_000`. -/
@[expose]
noncomputable def nb090AlphaDummy000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_001`. -/
@[expose]
noncomputable def nb090AlphaDummy001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_002`. -/
@[expose]
noncomputable def nb090AlphaDummy002 (A : Class) : Var :=
  (freshVar ((A).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_003`. -/
@[expose]
noncomputable def nb090AlphaDummy003 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy001 A)} : Finset Var) ∪
        ({(nb090AlphaDummy002 A)} : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
            (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A)))
          (synWex (nb090AlphaDummy000 A) (synWiso (Class.cv (nb090AlphaDummy000 A))
              (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
              (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
              (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
              (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_004`. -/
@[expose]
noncomputable def nb090AlphaDummy004 (v : Var) (u : Var) (A : Class) (h : Var) : Var :=
  (freshVar (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((synWa
          (synWa (Wff.classMem (Class.cv u) (synChwcodes A))
            (Wff.classMem (Class.cv v) (synChwcodes A))) (synWex h
            (synWiso (Class.cv h) (synCfv (synC1st) (Class.cv u))
              (synCfv (synC1st) (Class.cv v)) (synCfv (synC2nd) (Class.cv u))
              (synCfv (synC2nd) (Class.cv v)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_005`. -/
@[expose]
noncomputable def nb090AlphaDummy005 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy001 A))).fv ∪
      ((Class.cv (nb090AlphaDummy002 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_006`. -/
@[expose]
noncomputable def nb090AlphaDummy006 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy001 A))).fv ∪
      ((Class.cv (nb090AlphaDummy002 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_007`. -/
@[expose]
noncomputable def nb090AlphaDummy007 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_008`. -/
@[expose]
noncomputable def nb090AlphaDummy008 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_009`. -/
@[expose]
noncomputable def nb090AlphaDummy009 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCphi (Class.cv (nb090AlphaDummy006 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_010`. -/
@[expose]
noncomputable def nb090AlphaDummy010 (v : Var) (u : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCphi (Class.cv (nb090AlphaDummy008 v u)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_011`. -/
@[expose]
noncomputable def nb090AlphaDummy011 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy005 A)
          (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
              (synCphi (Class.cv (nb090AlphaDummy006 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy005 A)
          (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
              (synCphi (Class.cv (nb090AlphaDummy006 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_012`. -/
@[expose]
noncomputable def nb090AlphaDummy012 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy007 v u)
          (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
              (synCphi (Class.cv (nb090AlphaDummy008 v u))))))).fv ∪
      ((Class.cab (nb090AlphaDummy007 v u) (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
              (synCphi (Class.cv (nb090AlphaDummy008 v u))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_013`. -/
@[expose]
noncomputable def nb090AlphaDummy013 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy006 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_014`. -/
@[expose]
noncomputable def nb090AlphaDummy014 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy006 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_015`. -/
@[expose]
noncomputable def nb090AlphaDummy015 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy008 v u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_016`. -/
@[expose]
noncomputable def nb090AlphaDummy016 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy008 v u))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_017`. -/
@[expose]
noncomputable def nb090AlphaDummy017 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy013 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy013 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy013 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_018`. -/
@[expose]
noncomputable def nb090AlphaDummy018 (v : Var) (u : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy015 v u)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy015 v u)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy015 v u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_019`. -/
@[expose]
noncomputable def nb090AlphaDummy019 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_020`. -/
@[expose]
noncomputable def nb090AlphaDummy020 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_021`. -/
@[expose]
noncomputable def nb090AlphaDummy021 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_022`. -/
@[expose]
noncomputable def nb090AlphaDummy022 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_023`. -/
@[expose]
noncomputable def nb090AlphaDummy023 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_024`. -/
@[expose]
noncomputable def nb090AlphaDummy024 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_025`. -/
@[expose]
noncomputable def nb090AlphaDummy025 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy020 A))
          (Class.cv (nb090AlphaDummy021 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy020 A)) (Class.cv (nb090AlphaDummy021 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_026`. -/
@[expose]
noncomputable def nb090AlphaDummy026 (v : Var) (u : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy023 v u))
          (Class.cv (nb090AlphaDummy024 v u)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy023 v u))
          (Class.cv (nb090AlphaDummy024 v u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_027`. -/
@[expose]
noncomputable def nb090AlphaDummy027 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy020 A))).fv ∪
      ((Class.cv (nb090AlphaDummy021 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_028`. -/
@[expose]
noncomputable def nb090AlphaDummy028 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
      ((Class.cv (nb090AlphaDummy024 v u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_029`. -/
@[expose]
noncomputable def nb090AlphaDummy029 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy020 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy021 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_030`. -/
@[expose]
noncomputable def nb090AlphaDummy030 (v : Var) (u : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy023 v u)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy024 v u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_031`. -/
@[expose]
noncomputable def nb090AlphaDummy031 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy020 A))).fv ∪
      ((Class.cv (nb090AlphaDummy020 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_032`. -/
@[expose]
noncomputable def nb090AlphaDummy032 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
      ((Class.cv (nb090AlphaDummy023 v u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_033`. -/
@[expose]
noncomputable def nb090AlphaDummy033 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy021 A))).fv ∪
      ((Class.cv (nb090AlphaDummy021 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_034`. -/
@[expose]
noncomputable def nb090AlphaDummy034 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy024 v u))).fv ∪
      ((Class.cv (nb090AlphaDummy024 v u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_035`. -/
@[expose]
noncomputable def nb090AlphaDummy035 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy005 A)
          (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy005 A)
          (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_036`. -/
@[expose]
noncomputable def nb090AlphaDummy036 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy007 v u)
          (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
            (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
              (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy007 v u)
          (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
            (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
              (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_037`. -/
@[expose]
noncomputable def nb090AlphaDummy037 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy006 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_038`. -/
@[expose]
noncomputable def nb090AlphaDummy038 (v : Var) (u : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy008 v u))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_039`. -/
@[expose]
noncomputable def nb090AlphaDummy039 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy006 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy006 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_040`. -/
@[expose]
noncomputable def nb090AlphaDummy040 (v : Var) (u : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy008 v u)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy008 v u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_041`. -/
@[expose]
noncomputable def nb090AlphaDummy041 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
          ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
      ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_042`. -/
@[expose]
noncomputable def nb090AlphaDummy042 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
          ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
      ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_043`. -/
@[expose]
noncomputable def nb090AlphaDummy043 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
          ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
      ((synCfv (synC2nd) (Class.cv v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_044`. -/
@[expose]
noncomputable def nb090AlphaDummy044 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
          ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
      ((synCfv (synC2nd) (Class.cv v))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_045`. -/
@[expose]
noncomputable def nb090AlphaDummy045 (A : Class) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb090AlphaDummy000 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))).fv ∪ ((synCnin
          (synCcom (Class.cv (nb090AlphaDummy000 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_046`. -/
@[expose]
noncomputable def nb090AlphaDummy046 (h : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_047`. -/
@[expose]
noncomputable def nb090AlphaDummy047 (A : Class) : Var :=
  (freshVar (((synCcom (Class.cv (nb090AlphaDummy000 A))
          (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_048`. -/
@[expose]
noncomputable def nb090AlphaDummy048 (h : Var) : Var :=
  (freshVar (((synCcom (Class.cv h) (synCcnv (Class.cv h)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_049`. -/
@[expose]
noncomputable def nb090AlphaDummy049 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪
      ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_050`. -/
@[expose]
noncomputable def nb090AlphaDummy050 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪
      ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_051`. -/
@[expose]
noncomputable def nb090AlphaDummy051 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪
      ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_052`. -/
@[expose]
noncomputable def nb090AlphaDummy052 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_053`. -/
@[expose]
noncomputable def nb090AlphaDummy053 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_054`. -/
@[expose]
noncomputable def nb090AlphaDummy054 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_055`. -/
@[expose]
noncomputable def nb090AlphaDummy055 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy049 A)} : Finset Var) ∪
        ({(nb090AlphaDummy050 A)} : Finset Var) ∪ ((synWex (nb090AlphaDummy051 A) (synWa
            (synWbr (Class.cv (nb090AlphaDummy049 A))
              (synCcnv (Class.cv (nb090AlphaDummy000 A)))
              (Class.cv (nb090AlphaDummy051 A)))
            (synWbr (Class.cv (nb090AlphaDummy051 A)) (Class.cv (nb090AlphaDummy000 A))
              (Class.cv (nb090AlphaDummy050 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_056`. -/
@[expose]
noncomputable def nb090AlphaDummy056 (h : Var) : Var :=
  (freshVar (({(nb090AlphaDummy052 h)} : Finset Var) ∪
        ({(nb090AlphaDummy053 h)} : Finset Var) ∪ ((synWex (nb090AlphaDummy054 h) (synWa
            (synWbr (Class.cv (nb090AlphaDummy052 h)) (synCcnv (Class.cv h))
              (Class.cv (nb090AlphaDummy054 h)))
            (synWbr (Class.cv (nb090AlphaDummy054 h)) (Class.cv h)
              (Class.cv (nb090AlphaDummy053 h)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_057`. -/
@[expose]
noncomputable def nb090AlphaDummy057 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy049 A))).fv ∪
      ((Class.cv (nb090AlphaDummy050 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_058`. -/
@[expose]
noncomputable def nb090AlphaDummy058 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy049 A))).fv ∪
      ((Class.cv (nb090AlphaDummy050 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_059`. -/
@[expose]
noncomputable def nb090AlphaDummy059 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy052 h))).fv ∪
      ((Class.cv (nb090AlphaDummy053 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_060`. -/
@[expose]
noncomputable def nb090AlphaDummy060 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy052 h))).fv ∪
      ((Class.cv (nb090AlphaDummy053 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_061`. -/
@[expose]
noncomputable def nb090AlphaDummy061 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCphi (Class.cv (nb090AlphaDummy058 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_062`. -/
@[expose]
noncomputable def nb090AlphaDummy062 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCphi (Class.cv (nb090AlphaDummy060 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_063`. -/
@[expose]
noncomputable def nb090AlphaDummy063 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy057 A)
          (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
              (synCphi (Class.cv (nb090AlphaDummy058 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy057 A)
          (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
              (synCphi (Class.cv (nb090AlphaDummy058 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_064`. -/
@[expose]
noncomputable def nb090AlphaDummy064 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy059 h)
          (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
              (synCphi (Class.cv (nb090AlphaDummy060 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy059 h)
          (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
              (synCphi (Class.cv (nb090AlphaDummy060 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_065`. -/
@[expose]
noncomputable def nb090AlphaDummy065 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy058 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_066`. -/
@[expose]
noncomputable def nb090AlphaDummy066 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy058 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_067`. -/
@[expose]
noncomputable def nb090AlphaDummy067 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy060 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_068`. -/
@[expose]
noncomputable def nb090AlphaDummy068 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy060 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_069`. -/
@[expose]
noncomputable def nb090AlphaDummy069 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy065 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy065 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy065 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_070`. -/
@[expose]
noncomputable def nb090AlphaDummy070 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy067 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy067 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy067 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_071`. -/
@[expose]
noncomputable def nb090AlphaDummy071 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_072`. -/
@[expose]
noncomputable def nb090AlphaDummy072 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_073`. -/
@[expose]
noncomputable def nb090AlphaDummy073 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_074`. -/
@[expose]
noncomputable def nb090AlphaDummy074 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_075`. -/
@[expose]
noncomputable def nb090AlphaDummy075 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_076`. -/
@[expose]
noncomputable def nb090AlphaDummy076 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_077`. -/
@[expose]
noncomputable def nb090AlphaDummy077 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy072 A))
          (Class.cv (nb090AlphaDummy073 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy072 A)) (Class.cv (nb090AlphaDummy073 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_078`. -/
@[expose]
noncomputable def nb090AlphaDummy078 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy075 h))
          (Class.cv (nb090AlphaDummy076 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy075 h)) (Class.cv (nb090AlphaDummy076 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_079`. -/
@[expose]
noncomputable def nb090AlphaDummy079 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy072 A))).fv ∪
      ((Class.cv (nb090AlphaDummy073 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_080`. -/
@[expose]
noncomputable def nb090AlphaDummy080 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy075 h))).fv ∪
      ((Class.cv (nb090AlphaDummy076 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_081`. -/
@[expose]
noncomputable def nb090AlphaDummy081 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy072 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy073 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_082`. -/
@[expose]
noncomputable def nb090AlphaDummy082 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy075 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy076 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_083`. -/
@[expose]
noncomputable def nb090AlphaDummy083 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy072 A))).fv ∪
      ((Class.cv (nb090AlphaDummy072 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_084`. -/
@[expose]
noncomputable def nb090AlphaDummy084 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy075 h))).fv ∪
      ((Class.cv (nb090AlphaDummy075 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_085`. -/
@[expose]
noncomputable def nb090AlphaDummy085 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy073 A))).fv ∪
      ((Class.cv (nb090AlphaDummy073 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_086`. -/
@[expose]
noncomputable def nb090AlphaDummy086 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy076 h))).fv ∪
      ((Class.cv (nb090AlphaDummy076 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_087`. -/
@[expose]
noncomputable def nb090AlphaDummy087 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy057 A)
          (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy057 A)
          (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_088`. -/
@[expose]
noncomputable def nb090AlphaDummy088 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy059 h)
          (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy059 h)
          (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_089`. -/
@[expose]
noncomputable def nb090AlphaDummy089 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy058 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_090`. -/
@[expose]
noncomputable def nb090AlphaDummy090 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy060 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_091`. -/
@[expose]
noncomputable def nb090AlphaDummy091 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy058 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy058 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_092`. -/
@[expose]
noncomputable def nb090AlphaDummy092 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy060 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy060 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_093`. -/
@[expose]
noncomputable def nb090AlphaDummy093 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy049 A))).fv ∪
      ((Class.cv (nb090AlphaDummy051 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_094`. -/
@[expose]
noncomputable def nb090AlphaDummy094 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy049 A))).fv ∪
      ((Class.cv (nb090AlphaDummy051 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_095`. -/
@[expose]
noncomputable def nb090AlphaDummy095 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy052 h))).fv ∪
      ((Class.cv (nb090AlphaDummy054 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_096`. -/
@[expose]
noncomputable def nb090AlphaDummy096 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy052 h))).fv ∪
      ((Class.cv (nb090AlphaDummy054 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_097`. -/
@[expose]
noncomputable def nb090AlphaDummy097 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCphi (Class.cv (nb090AlphaDummy094 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_098`. -/
@[expose]
noncomputable def nb090AlphaDummy098 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCphi (Class.cv (nb090AlphaDummy096 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_099`. -/
@[expose]
noncomputable def nb090AlphaDummy099 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy093 A)
          (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
              (synCphi (Class.cv (nb090AlphaDummy094 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy093 A)
          (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
              (synCphi (Class.cv (nb090AlphaDummy094 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_100`. -/
@[expose]
noncomputable def nb090AlphaDummy100 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy095 h)
          (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
              (synCphi (Class.cv (nb090AlphaDummy096 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy095 h)
          (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
              (synCphi (Class.cv (nb090AlphaDummy096 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_101`. -/
@[expose]
noncomputable def nb090AlphaDummy101 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy094 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_102`. -/
@[expose]
noncomputable def nb090AlphaDummy102 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy094 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_103`. -/
@[expose]
noncomputable def nb090AlphaDummy103 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy096 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_104`. -/
@[expose]
noncomputable def nb090AlphaDummy104 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy096 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_105`. -/
@[expose]
noncomputable def nb090AlphaDummy105 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy101 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy101 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy101 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_106`. -/
@[expose]
noncomputable def nb090AlphaDummy106 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy103 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy103 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy103 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_107`. -/
@[expose]
noncomputable def nb090AlphaDummy107 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_108`. -/
@[expose]
noncomputable def nb090AlphaDummy108 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_109`. -/
@[expose]
noncomputable def nb090AlphaDummy109 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_110`. -/
@[expose]
noncomputable def nb090AlphaDummy110 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_111`. -/
@[expose]
noncomputable def nb090AlphaDummy111 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_112`. -/
@[expose]
noncomputable def nb090AlphaDummy112 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_113`. -/
@[expose]
noncomputable def nb090AlphaDummy113 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy108 A))
          (Class.cv (nb090AlphaDummy109 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy108 A)) (Class.cv (nb090AlphaDummy109 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_114`. -/
@[expose]
noncomputable def nb090AlphaDummy114 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy111 h))
          (Class.cv (nb090AlphaDummy112 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy111 h)) (Class.cv (nb090AlphaDummy112 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_115`. -/
@[expose]
noncomputable def nb090AlphaDummy115 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy108 A))).fv ∪
      ((Class.cv (nb090AlphaDummy109 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_116`. -/
@[expose]
noncomputable def nb090AlphaDummy116 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy111 h))).fv ∪
      ((Class.cv (nb090AlphaDummy112 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_117`. -/
@[expose]
noncomputable def nb090AlphaDummy117 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy108 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy109 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_118`. -/
@[expose]
noncomputable def nb090AlphaDummy118 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy111 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy112 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_119`. -/
@[expose]
noncomputable def nb090AlphaDummy119 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy108 A))).fv ∪
      ((Class.cv (nb090AlphaDummy108 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_120`. -/
@[expose]
noncomputable def nb090AlphaDummy120 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy111 h))).fv ∪
      ((Class.cv (nb090AlphaDummy111 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_121`. -/
@[expose]
noncomputable def nb090AlphaDummy121 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy109 A))).fv ∪
      ((Class.cv (nb090AlphaDummy109 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_122`. -/
@[expose]
noncomputable def nb090AlphaDummy122 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy112 h))).fv ∪
      ((Class.cv (nb090AlphaDummy112 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_123`. -/
@[expose]
noncomputable def nb090AlphaDummy123 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy093 A)
          (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy093 A)
          (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_124`. -/
@[expose]
noncomputable def nb090AlphaDummy124 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy095 h)
          (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy095 h)
          (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_125`. -/
@[expose]
noncomputable def nb090AlphaDummy125 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy094 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_126`. -/
@[expose]
noncomputable def nb090AlphaDummy126 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy096 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_127`. -/
@[expose]
noncomputable def nb090AlphaDummy127 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy094 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy094 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_128`. -/
@[expose]
noncomputable def nb090AlphaDummy128 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy096 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy096 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_129`. -/
@[expose]
noncomputable def nb090AlphaDummy129 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_130`. -/
@[expose]
noncomputable def nb090AlphaDummy130 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_131`. -/
@[expose]
noncomputable def nb090AlphaDummy131 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_132`. -/
@[expose]
noncomputable def nb090AlphaDummy132 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_133`. -/
@[expose]
noncomputable def nb090AlphaDummy133 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy129 A)} : Finset Var) ∪
        ({(nb090AlphaDummy130 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy130 A)) (Class.cv (nb090AlphaDummy000 A))
          (Class.cv (nb090AlphaDummy129 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_134`. -/
@[expose]
noncomputable def nb090AlphaDummy134 (h : Var) : Var :=
  (freshVar (({(nb090AlphaDummy131 h)} : Finset Var) ∪
        ({(nb090AlphaDummy132 h)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy132 h)) (Class.cv h)
          (Class.cv (nb090AlphaDummy131 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_135`. -/
@[expose]
noncomputable def nb090AlphaDummy135 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy129 A))).fv ∪
      ((Class.cv (nb090AlphaDummy130 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_136`. -/
@[expose]
noncomputable def nb090AlphaDummy136 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy129 A))).fv ∪
      ((Class.cv (nb090AlphaDummy130 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_137`. -/
@[expose]
noncomputable def nb090AlphaDummy137 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy131 h))).fv ∪
      ((Class.cv (nb090AlphaDummy132 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_138`. -/
@[expose]
noncomputable def nb090AlphaDummy138 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy131 h))).fv ∪
      ((Class.cv (nb090AlphaDummy132 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_139`. -/
@[expose]
noncomputable def nb090AlphaDummy139 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_140`. -/
@[expose]
noncomputable def nb090AlphaDummy140 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_141`. -/
@[expose]
noncomputable def nb090AlphaDummy141 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy135 A)
          (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
              (synCphi (Class.cv (nb090AlphaDummy136 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy135 A)
          (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
              (synCphi (Class.cv (nb090AlphaDummy136 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_142`. -/
@[expose]
noncomputable def nb090AlphaDummy142 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy137 h)
          (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
              (synCphi (Class.cv (nb090AlphaDummy138 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy137 h)
          (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
              (synCphi (Class.cv (nb090AlphaDummy138 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_143`. -/
@[expose]
noncomputable def nb090AlphaDummy143 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy136 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_144`. -/
@[expose]
noncomputable def nb090AlphaDummy144 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy136 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_145`. -/
@[expose]
noncomputable def nb090AlphaDummy145 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy138 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_146`. -/
@[expose]
noncomputable def nb090AlphaDummy146 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy138 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_147`. -/
@[expose]
noncomputable def nb090AlphaDummy147 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy143 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy143 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy143 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_148`. -/
@[expose]
noncomputable def nb090AlphaDummy148 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy145 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy145 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy145 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_149`. -/
@[expose]
noncomputable def nb090AlphaDummy149 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_150`. -/
@[expose]
noncomputable def nb090AlphaDummy150 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_151`. -/
@[expose]
noncomputable def nb090AlphaDummy151 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_152`. -/
@[expose]
noncomputable def nb090AlphaDummy152 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_153`. -/
@[expose]
noncomputable def nb090AlphaDummy153 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_154`. -/
@[expose]
noncomputable def nb090AlphaDummy154 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_155`. -/
@[expose]
noncomputable def nb090AlphaDummy155 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy150 A))
          (Class.cv (nb090AlphaDummy151 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy150 A)) (Class.cv (nb090AlphaDummy151 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_156`. -/
@[expose]
noncomputable def nb090AlphaDummy156 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy153 h))
          (Class.cv (nb090AlphaDummy154 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy153 h)) (Class.cv (nb090AlphaDummy154 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_157`. -/
@[expose]
noncomputable def nb090AlphaDummy157 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy150 A))).fv ∪
      ((Class.cv (nb090AlphaDummy151 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_158`. -/
@[expose]
noncomputable def nb090AlphaDummy158 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy153 h))).fv ∪
      ((Class.cv (nb090AlphaDummy154 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_159`. -/
@[expose]
noncomputable def nb090AlphaDummy159 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy150 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy151 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_160`. -/
@[expose]
noncomputable def nb090AlphaDummy160 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy153 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy154 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_161`. -/
@[expose]
noncomputable def nb090AlphaDummy161 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy150 A))).fv ∪
      ((Class.cv (nb090AlphaDummy150 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_162`. -/
@[expose]
noncomputable def nb090AlphaDummy162 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy153 h))).fv ∪
      ((Class.cv (nb090AlphaDummy153 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_163`. -/
@[expose]
noncomputable def nb090AlphaDummy163 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy151 A))).fv ∪
      ((Class.cv (nb090AlphaDummy151 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_164`. -/
@[expose]
noncomputable def nb090AlphaDummy164 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy154 h))).fv ∪
      ((Class.cv (nb090AlphaDummy154 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_165`. -/
@[expose]
noncomputable def nb090AlphaDummy165 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy135 A)
          (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy135 A)
          (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_166`. -/
@[expose]
noncomputable def nb090AlphaDummy166 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy137 h)
          (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy137 h)
          (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_167`. -/
@[expose]
noncomputable def nb090AlphaDummy167 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy136 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_168`. -/
@[expose]
noncomputable def nb090AlphaDummy168 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy138 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_169`. -/
@[expose]
noncomputable def nb090AlphaDummy169 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy136 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy136 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_170`. -/
@[expose]
noncomputable def nb090AlphaDummy170 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy138 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy138 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_171`. -/
@[expose]
noncomputable def nb090AlphaDummy171 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy130 A))).fv ∪
      ((Class.cv (nb090AlphaDummy129 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_172`. -/
@[expose]
noncomputable def nb090AlphaDummy172 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy130 A))).fv ∪
      ((Class.cv (nb090AlphaDummy129 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_173`. -/
@[expose]
noncomputable def nb090AlphaDummy173 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy132 h))).fv ∪
      ((Class.cv (nb090AlphaDummy131 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_174`. -/
@[expose]
noncomputable def nb090AlphaDummy174 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy132 h))).fv ∪
      ((Class.cv (nb090AlphaDummy131 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_175`. -/
@[expose]
noncomputable def nb090AlphaDummy175 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_176`. -/
@[expose]
noncomputable def nb090AlphaDummy176 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_177`. -/
@[expose]
noncomputable def nb090AlphaDummy177 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy171 A)
          (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
              (synCphi (Class.cv (nb090AlphaDummy172 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy171 A)
          (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
              (synCphi (Class.cv (nb090AlphaDummy172 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_178`. -/
@[expose]
noncomputable def nb090AlphaDummy178 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy173 h)
          (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
              (synCphi (Class.cv (nb090AlphaDummy174 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy173 h)
          (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
              (synCphi (Class.cv (nb090AlphaDummy174 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_179`. -/
@[expose]
noncomputable def nb090AlphaDummy179 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy172 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_180`. -/
@[expose]
noncomputable def nb090AlphaDummy180 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy172 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_181`. -/
@[expose]
noncomputable def nb090AlphaDummy181 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy174 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_182`. -/
@[expose]
noncomputable def nb090AlphaDummy182 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy174 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_183`. -/
@[expose]
noncomputable def nb090AlphaDummy183 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy179 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy179 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy179 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_184`. -/
@[expose]
noncomputable def nb090AlphaDummy184 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy181 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy181 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy181 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_185`. -/
@[expose]
noncomputable def nb090AlphaDummy185 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_186`. -/
@[expose]
noncomputable def nb090AlphaDummy186 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_187`. -/
@[expose]
noncomputable def nb090AlphaDummy187 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_188`. -/
@[expose]
noncomputable def nb090AlphaDummy188 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_189`. -/
@[expose]
noncomputable def nb090AlphaDummy189 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_190`. -/
@[expose]
noncomputable def nb090AlphaDummy190 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_191`. -/
@[expose]
noncomputable def nb090AlphaDummy191 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy186 A))
          (Class.cv (nb090AlphaDummy187 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy186 A)) (Class.cv (nb090AlphaDummy187 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_192`. -/
@[expose]
noncomputable def nb090AlphaDummy192 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy189 h))
          (Class.cv (nb090AlphaDummy190 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy189 h)) (Class.cv (nb090AlphaDummy190 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_193`. -/
@[expose]
noncomputable def nb090AlphaDummy193 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy186 A))).fv ∪
      ((Class.cv (nb090AlphaDummy187 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_194`. -/
@[expose]
noncomputable def nb090AlphaDummy194 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy189 h))).fv ∪
      ((Class.cv (nb090AlphaDummy190 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_195`. -/
@[expose]
noncomputable def nb090AlphaDummy195 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy186 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy187 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_196`. -/
@[expose]
noncomputable def nb090AlphaDummy196 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy189 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy190 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_197`. -/
@[expose]
noncomputable def nb090AlphaDummy197 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy186 A))).fv ∪
      ((Class.cv (nb090AlphaDummy186 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_198`. -/
@[expose]
noncomputable def nb090AlphaDummy198 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy189 h))).fv ∪
      ((Class.cv (nb090AlphaDummy189 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_199`. -/
@[expose]
noncomputable def nb090AlphaDummy199 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy187 A))).fv ∪
      ((Class.cv (nb090AlphaDummy187 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_200`. -/
@[expose]
noncomputable def nb090AlphaDummy200 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy190 h))).fv ∪
      ((Class.cv (nb090AlphaDummy190 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_201`. -/
@[expose]
noncomputable def nb090AlphaDummy201 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy171 A)
          (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy171 A)
          (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_202`. -/
@[expose]
noncomputable def nb090AlphaDummy202 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy173 h)
          (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy173 h)
          (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_203`. -/
@[expose]
noncomputable def nb090AlphaDummy203 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy172 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_204`. -/
@[expose]
noncomputable def nb090AlphaDummy204 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy174 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_205`. -/
@[expose]
noncomputable def nb090AlphaDummy205 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy172 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy172 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_206`. -/
@[expose]
noncomputable def nb090AlphaDummy206 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy174 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy174 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_207`. -/
@[expose]
noncomputable def nb090AlphaDummy207 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy051 A))).fv ∪
      ((Class.cv (nb090AlphaDummy050 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_208`. -/
@[expose]
noncomputable def nb090AlphaDummy208 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy051 A))).fv ∪
      ((Class.cv (nb090AlphaDummy050 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_209`. -/
@[expose]
noncomputable def nb090AlphaDummy209 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy054 h))).fv ∪
      ((Class.cv (nb090AlphaDummy053 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_210`. -/
@[expose]
noncomputable def nb090AlphaDummy210 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy054 h))).fv ∪
      ((Class.cv (nb090AlphaDummy053 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_211`. -/
@[expose]
noncomputable def nb090AlphaDummy211 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCphi (Class.cv (nb090AlphaDummy208 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_212`. -/
@[expose]
noncomputable def nb090AlphaDummy212 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCphi (Class.cv (nb090AlphaDummy210 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_213`. -/
@[expose]
noncomputable def nb090AlphaDummy213 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy207 A)
          (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
              (synCphi (Class.cv (nb090AlphaDummy208 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy207 A)
          (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
              (synCphi (Class.cv (nb090AlphaDummy208 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_214`. -/
@[expose]
noncomputable def nb090AlphaDummy214 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy209 h)
          (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
              (synCphi (Class.cv (nb090AlphaDummy210 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy209 h)
          (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
              (synCphi (Class.cv (nb090AlphaDummy210 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_215`. -/
@[expose]
noncomputable def nb090AlphaDummy215 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy208 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_216`. -/
@[expose]
noncomputable def nb090AlphaDummy216 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy208 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_217`. -/
@[expose]
noncomputable def nb090AlphaDummy217 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy210 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_218`. -/
@[expose]
noncomputable def nb090AlphaDummy218 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy210 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_219`. -/
@[expose]
noncomputable def nb090AlphaDummy219 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy215 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy215 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy215 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_220`. -/
@[expose]
noncomputable def nb090AlphaDummy220 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy217 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy217 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy217 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_221`. -/
@[expose]
noncomputable def nb090AlphaDummy221 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_222`. -/
@[expose]
noncomputable def nb090AlphaDummy222 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_223`. -/
@[expose]
noncomputable def nb090AlphaDummy223 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_224`. -/
@[expose]
noncomputable def nb090AlphaDummy224 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_225`. -/
@[expose]
noncomputable def nb090AlphaDummy225 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_226`. -/
@[expose]
noncomputable def nb090AlphaDummy226 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_227`. -/
@[expose]
noncomputable def nb090AlphaDummy227 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy222 A))
          (Class.cv (nb090AlphaDummy223 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy222 A)) (Class.cv (nb090AlphaDummy223 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_228`. -/
@[expose]
noncomputable def nb090AlphaDummy228 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy225 h))
          (Class.cv (nb090AlphaDummy226 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy225 h)) (Class.cv (nb090AlphaDummy226 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_229`. -/
@[expose]
noncomputable def nb090AlphaDummy229 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy222 A))).fv ∪
      ((Class.cv (nb090AlphaDummy223 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_230`. -/
@[expose]
noncomputable def nb090AlphaDummy230 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy225 h))).fv ∪
      ((Class.cv (nb090AlphaDummy226 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_231`. -/
@[expose]
noncomputable def nb090AlphaDummy231 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy222 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy223 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_232`. -/
@[expose]
noncomputable def nb090AlphaDummy232 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy225 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy226 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_233`. -/
@[expose]
noncomputable def nb090AlphaDummy233 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy222 A))).fv ∪
      ((Class.cv (nb090AlphaDummy222 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_234`. -/
@[expose]
noncomputable def nb090AlphaDummy234 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy225 h))).fv ∪
      ((Class.cv (nb090AlphaDummy225 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_235`. -/
@[expose]
noncomputable def nb090AlphaDummy235 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy223 A))).fv ∪
      ((Class.cv (nb090AlphaDummy223 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_236`. -/
@[expose]
noncomputable def nb090AlphaDummy236 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy226 h))).fv ∪
      ((Class.cv (nb090AlphaDummy226 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_237`. -/
@[expose]
noncomputable def nb090AlphaDummy237 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy207 A)
          (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy207 A)
          (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_238`. -/
@[expose]
noncomputable def nb090AlphaDummy238 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy209 h)
          (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy209 h)
          (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_239`. -/
@[expose]
noncomputable def nb090AlphaDummy239 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy208 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_240`. -/
@[expose]
noncomputable def nb090AlphaDummy240 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy210 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_241`. -/
@[expose]
noncomputable def nb090AlphaDummy241 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy208 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy208 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_242`. -/
@[expose]
noncomputable def nb090AlphaDummy242 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy210 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy210 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_243`. -/
@[expose]
noncomputable def nb090AlphaDummy243 (A : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_244`. -/
@[expose]
noncomputable def nb090AlphaDummy244 (A : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_245`. -/
@[expose]
noncomputable def nb090AlphaDummy245 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_246`. -/
@[expose]
noncomputable def nb090AlphaDummy246 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_247`. -/
@[expose]
noncomputable def nb090AlphaDummy247 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy244 A))).fv ∪
      ((Class.cv (nb090AlphaDummy243 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_248`. -/
@[expose]
noncomputable def nb090AlphaDummy248 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy244 A))).fv ∪
      ((Class.cv (nb090AlphaDummy243 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_249`. -/
@[expose]
noncomputable def nb090AlphaDummy249 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy246 h))).fv ∪
      ((Class.cv (nb090AlphaDummy245 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_250`. -/
@[expose]
noncomputable def nb090AlphaDummy250 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy246 h))).fv ∪
      ((Class.cv (nb090AlphaDummy245 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_251`. -/
@[expose]
noncomputable def nb090AlphaDummy251 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCphi (Class.cv (nb090AlphaDummy248 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_252`. -/
@[expose]
noncomputable def nb090AlphaDummy252 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCphi (Class.cv (nb090AlphaDummy250 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_253`. -/
@[expose]
noncomputable def nb090AlphaDummy253 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy247 A)
          (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
              (synCphi (Class.cv (nb090AlphaDummy248 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy247 A)
          (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
              (synCphi (Class.cv (nb090AlphaDummy248 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_254`. -/
@[expose]
noncomputable def nb090AlphaDummy254 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy249 h)
          (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
              (synCphi (Class.cv (nb090AlphaDummy250 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy249 h)
          (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
              (synCphi (Class.cv (nb090AlphaDummy250 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_255`. -/
@[expose]
noncomputable def nb090AlphaDummy255 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy248 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_256`. -/
@[expose]
noncomputable def nb090AlphaDummy256 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy248 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_257`. -/
@[expose]
noncomputable def nb090AlphaDummy257 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy250 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_258`. -/
@[expose]
noncomputable def nb090AlphaDummy258 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy250 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_259`. -/
@[expose]
noncomputable def nb090AlphaDummy259 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy255 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy255 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy255 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_260`. -/
@[expose]
noncomputable def nb090AlphaDummy260 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy257 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy257 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy257 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_261`. -/
@[expose]
noncomputable def nb090AlphaDummy261 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_262`. -/
@[expose]
noncomputable def nb090AlphaDummy262 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_263`. -/
@[expose]
noncomputable def nb090AlphaDummy263 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_264`. -/
@[expose]
noncomputable def nb090AlphaDummy264 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_265`. -/
@[expose]
noncomputable def nb090AlphaDummy265 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_266`. -/
@[expose]
noncomputable def nb090AlphaDummy266 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_267`. -/
@[expose]
noncomputable def nb090AlphaDummy267 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy262 A))
          (Class.cv (nb090AlphaDummy263 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy262 A)) (Class.cv (nb090AlphaDummy263 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_268`. -/
@[expose]
noncomputable def nb090AlphaDummy268 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy265 h))
          (Class.cv (nb090AlphaDummy266 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy265 h)) (Class.cv (nb090AlphaDummy266 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_269`. -/
@[expose]
noncomputable def nb090AlphaDummy269 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy262 A))).fv ∪
      ((Class.cv (nb090AlphaDummy263 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_270`. -/
@[expose]
noncomputable def nb090AlphaDummy270 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy265 h))).fv ∪
      ((Class.cv (nb090AlphaDummy266 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_271`. -/
@[expose]
noncomputable def nb090AlphaDummy271 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy262 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy263 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_272`. -/
@[expose]
noncomputable def nb090AlphaDummy272 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy265 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy266 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_273`. -/
@[expose]
noncomputable def nb090AlphaDummy273 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy262 A))).fv ∪
      ((Class.cv (nb090AlphaDummy262 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_274`. -/
@[expose]
noncomputable def nb090AlphaDummy274 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy265 h))).fv ∪
      ((Class.cv (nb090AlphaDummy265 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_275`. -/
@[expose]
noncomputable def nb090AlphaDummy275 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy263 A))).fv ∪
      ((Class.cv (nb090AlphaDummy263 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_276`. -/
@[expose]
noncomputable def nb090AlphaDummy276 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy266 h))).fv ∪
      ((Class.cv (nb090AlphaDummy266 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_277`. -/
@[expose]
noncomputable def nb090AlphaDummy277 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy247 A)
          (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy247 A)
          (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_278`. -/
@[expose]
noncomputable def nb090AlphaDummy278 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy249 h)
          (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy249 h)
          (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_279`. -/
@[expose]
noncomputable def nb090AlphaDummy279 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy248 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_280`. -/
@[expose]
noncomputable def nb090AlphaDummy280 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy250 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_281`. -/
@[expose]
noncomputable def nb090AlphaDummy281 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy248 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy248 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_282`. -/
@[expose]
noncomputable def nb090AlphaDummy282 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy250 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy250 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_283`. -/
@[expose]
noncomputable def nb090AlphaDummy283 (A : Class) : Var :=
  (freshVar (((synC2nd)).fv ∪ ((Class.cv (nb090AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_284`. -/
@[expose]
noncomputable def nb090AlphaDummy284 (u : Var) : Var :=
  (freshVar (((synC2nd)).fv ∪ ((Class.cv u)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_285`. -/
@[expose]
noncomputable def nb090AlphaDummy285 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy283 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
          (Class.cv (nb090AlphaDummy283 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_286`. -/
@[expose]
noncomputable def nb090AlphaDummy286 (u : Var) : Var :=
  (freshVar (({(nb090AlphaDummy284 u)} : Finset Var) ∪
      ((synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_287`. -/
@[expose]
noncomputable def nb090AlphaDummy287 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy283 A)
            (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
              (Class.cv (nb090AlphaDummy283 A))))
          (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_288`. -/
@[expose]
noncomputable def nb090AlphaDummy288 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy283 A)
            (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
              (Class.cv (nb090AlphaDummy283 A))))
          (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_289`. -/
@[expose]
noncomputable def nb090AlphaDummy289 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq
          (Class.cab (nb090AlphaDummy284 u)
            (synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u))))
          (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_290`. -/
@[expose]
noncomputable def nb090AlphaDummy290 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq
          (Class.cab (nb090AlphaDummy284 u)
            (synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u))))
          (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_291`. -/
@[expose]
noncomputable def nb090AlphaDummy291 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy001 A))).fv ∪
      ((Class.cv (nb090AlphaDummy283 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_292`. -/
@[expose]
noncomputable def nb090AlphaDummy292 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy001 A))).fv ∪
      ((Class.cv (nb090AlphaDummy283 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_293`. -/
@[expose]
noncomputable def nb090AlphaDummy293 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_294`. -/
@[expose]
noncomputable def nb090AlphaDummy294 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_295`. -/
@[expose]
noncomputable def nb090AlphaDummy295 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCphi (Class.cv (nb090AlphaDummy292 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_296`. -/
@[expose]
noncomputable def nb090AlphaDummy296 (u : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy293 u)
            (synWrex (nb090AlphaDummy294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCphi (Class.cv (nb090AlphaDummy294 u)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy293 u)
            (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_297`. -/
@[expose]
noncomputable def nb090AlphaDummy297 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy291 A)
          (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
              (synCphi (Class.cv (nb090AlphaDummy292 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy291 A)
          (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
              (synCphi (Class.cv (nb090AlphaDummy292 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_298`. -/
@[expose]
noncomputable def nb090AlphaDummy298 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy293 u)
          (synWrex (nb090AlphaDummy294 u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
              (synCphi (Class.cv (nb090AlphaDummy294 u))))))).fv ∪
      ((Class.cab (nb090AlphaDummy293 u) (synWrex (nb090AlphaDummy294 u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
              (synCphi (Class.cv (nb090AlphaDummy294 u))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_299`. -/
@[expose]
noncomputable def nb090AlphaDummy299 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy292 A))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_300`. -/
@[expose]
noncomputable def nb090AlphaDummy300 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy292 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_301`. -/
@[expose]
noncomputable def nb090AlphaDummy301 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy294 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_302`. -/
@[expose]
noncomputable def nb090AlphaDummy302 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy294 u))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_303`. -/
@[expose]
noncomputable def nb090AlphaDummy303 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy299 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy299 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy299 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_304`. -/
@[expose]
noncomputable def nb090AlphaDummy304 (u : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy301 u)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy301 u)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy301 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_305`. -/
@[expose]
noncomputable def nb090AlphaDummy305 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_306`. -/
@[expose]
noncomputable def nb090AlphaDummy306 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_307`. -/
@[expose]
noncomputable def nb090AlphaDummy307 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_308`. -/
@[expose]
noncomputable def nb090AlphaDummy308 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_309`. -/
@[expose]
noncomputable def nb090AlphaDummy309 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_310`. -/
@[expose]
noncomputable def nb090AlphaDummy310 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_311`. -/
@[expose]
noncomputable def nb090AlphaDummy311 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy306 A))
          (Class.cv (nb090AlphaDummy307 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy306 A)) (Class.cv (nb090AlphaDummy307 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_312`. -/
@[expose]
noncomputable def nb090AlphaDummy312 (u : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy309 u))
          (Class.cv (nb090AlphaDummy310 u)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy309 u)) (Class.cv (nb090AlphaDummy310 u)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_313`. -/
@[expose]
noncomputable def nb090AlphaDummy313 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy306 A))).fv ∪
      ((Class.cv (nb090AlphaDummy307 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_314`. -/
@[expose]
noncomputable def nb090AlphaDummy314 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy309 u))).fv ∪
      ((Class.cv (nb090AlphaDummy310 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_315`. -/
@[expose]
noncomputable def nb090AlphaDummy315 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy306 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy307 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_316`. -/
@[expose]
noncomputable def nb090AlphaDummy316 (u : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy309 u)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy310 u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_317`. -/
@[expose]
noncomputable def nb090AlphaDummy317 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy306 A))).fv ∪
      ((Class.cv (nb090AlphaDummy306 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_318`. -/
@[expose]
noncomputable def nb090AlphaDummy318 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy309 u))).fv ∪
      ((Class.cv (nb090AlphaDummy309 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_319`. -/
@[expose]
noncomputable def nb090AlphaDummy319 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy307 A))).fv ∪
      ((Class.cv (nb090AlphaDummy307 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_320`. -/
@[expose]
noncomputable def nb090AlphaDummy320 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy310 u))).fv ∪
      ((Class.cv (nb090AlphaDummy310 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_321`. -/
@[expose]
noncomputable def nb090AlphaDummy321 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy291 A)
          (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy291 A)
          (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_322`. -/
@[expose]
noncomputable def nb090AlphaDummy322 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy293 u)
          (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
            (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
              (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy293 u)
          (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
            (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
              (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_323`. -/
@[expose]
noncomputable def nb090AlphaDummy323 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy292 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_324`. -/
@[expose]
noncomputable def nb090AlphaDummy324 (u : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy294 u))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_325`. -/
@[expose]
noncomputable def nb090AlphaDummy325 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy292 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy292 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_326`. -/
@[expose]
noncomputable def nb090AlphaDummy326 (u : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy294 u)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy294 u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_327`. -/
@[expose]
noncomputable def nb090AlphaDummy327 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy285 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_328`. -/
@[expose]
noncomputable def nb090AlphaDummy328 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy286 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_329`. -/
@[expose]
noncomputable def nb090AlphaDummy329 (A : Class) : Var :=
  (freshVar (((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
          (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv ∪
      ((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
          (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_330`. -/
@[expose]
noncomputable def nb090AlphaDummy330 (v : Var) (h : Var) : Var :=
  (freshVar (((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv ∪
      ((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_331`. -/
@[expose]
noncomputable def nb090AlphaDummy331 (A : Class) : Var :=
  (freshVar (((synCrn (Class.cv (nb090AlphaDummy000 A)))).fv ∪
      ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_332`. -/
@[expose]
noncomputable def nb090AlphaDummy332 (v : Var) (h : Var) : Var :=
  (freshVar (((synCrn (Class.cv h))).fv ∪ ((synCfv (synC2nd) (Class.cv v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_333`. -/
@[expose]
noncomputable def nb090AlphaDummy333 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_334`. -/
@[expose]
noncomputable def nb090AlphaDummy334 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_335`. -/
@[expose]
noncomputable def nb090AlphaDummy335 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_336`. -/
@[expose]
noncomputable def nb090AlphaDummy336 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_337`. -/
@[expose]
noncomputable def nb090AlphaDummy337 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy334 A))).fv ∪
      ((Class.cv (nb090AlphaDummy333 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_338`. -/
@[expose]
noncomputable def nb090AlphaDummy338 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy334 A))).fv ∪
      ((Class.cv (nb090AlphaDummy333 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_339`. -/
@[expose]
noncomputable def nb090AlphaDummy339 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy336 h))).fv ∪
      ((Class.cv (nb090AlphaDummy335 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_340`. -/
@[expose]
noncomputable def nb090AlphaDummy340 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy336 h))).fv ∪
      ((Class.cv (nb090AlphaDummy335 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_341`. -/
@[expose]
noncomputable def nb090AlphaDummy341 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCphi (Class.cv (nb090AlphaDummy338 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_342`. -/
@[expose]
noncomputable def nb090AlphaDummy342 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCphi (Class.cv (nb090AlphaDummy340 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_343`. -/
@[expose]
noncomputable def nb090AlphaDummy343 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy337 A)
          (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
              (synCphi (Class.cv (nb090AlphaDummy338 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy337 A)
          (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
              (synCphi (Class.cv (nb090AlphaDummy338 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_344`. -/
@[expose]
noncomputable def nb090AlphaDummy344 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy339 h)
          (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
              (synCphi (Class.cv (nb090AlphaDummy340 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy339 h)
          (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
              (synCphi (Class.cv (nb090AlphaDummy340 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_345`. -/
@[expose]
noncomputable def nb090AlphaDummy345 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy338 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_346`. -/
@[expose]
noncomputable def nb090AlphaDummy346 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy338 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_347`. -/
@[expose]
noncomputable def nb090AlphaDummy347 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy340 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_348`. -/
@[expose]
noncomputable def nb090AlphaDummy348 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy340 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_349`. -/
@[expose]
noncomputable def nb090AlphaDummy349 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy345 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy345 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy345 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_350`. -/
@[expose]
noncomputable def nb090AlphaDummy350 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy347 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy347 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy347 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_351`. -/
@[expose]
noncomputable def nb090AlphaDummy351 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_352`. -/
@[expose]
noncomputable def nb090AlphaDummy352 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_353`. -/
@[expose]
noncomputable def nb090AlphaDummy353 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_354`. -/
@[expose]
noncomputable def nb090AlphaDummy354 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_355`. -/
@[expose]
noncomputable def nb090AlphaDummy355 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_356`. -/
@[expose]
noncomputable def nb090AlphaDummy356 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_357`. -/
@[expose]
noncomputable def nb090AlphaDummy357 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy352 A))
          (Class.cv (nb090AlphaDummy353 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy352 A)) (Class.cv (nb090AlphaDummy353 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_358`. -/
@[expose]
noncomputable def nb090AlphaDummy358 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy355 h))
          (Class.cv (nb090AlphaDummy356 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy355 h)) (Class.cv (nb090AlphaDummy356 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_359`. -/
@[expose]
noncomputable def nb090AlphaDummy359 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy352 A))).fv ∪
      ((Class.cv (nb090AlphaDummy353 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_360`. -/
@[expose]
noncomputable def nb090AlphaDummy360 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy355 h))).fv ∪
      ((Class.cv (nb090AlphaDummy356 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_361`. -/
@[expose]
noncomputable def nb090AlphaDummy361 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy352 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy353 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_362`. -/
@[expose]
noncomputable def nb090AlphaDummy362 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy355 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy356 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_363`. -/
@[expose]
noncomputable def nb090AlphaDummy363 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy352 A))).fv ∪
      ((Class.cv (nb090AlphaDummy352 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_364`. -/
@[expose]
noncomputable def nb090AlphaDummy364 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy355 h))).fv ∪
      ((Class.cv (nb090AlphaDummy355 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_365`. -/
@[expose]
noncomputable def nb090AlphaDummy365 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy353 A))).fv ∪
      ((Class.cv (nb090AlphaDummy353 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_366`. -/
@[expose]
noncomputable def nb090AlphaDummy366 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy356 h))).fv ∪
      ((Class.cv (nb090AlphaDummy356 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_367`. -/
@[expose]
noncomputable def nb090AlphaDummy367 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy337 A)
          (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy337 A)
          (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_368`. -/
@[expose]
noncomputable def nb090AlphaDummy368 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy339 h)
          (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy339 h)
          (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_369`. -/
@[expose]
noncomputable def nb090AlphaDummy369 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy338 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_370`. -/
@[expose]
noncomputable def nb090AlphaDummy370 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy340 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_371`. -/
@[expose]
noncomputable def nb090AlphaDummy371 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy338 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy338 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_372`. -/
@[expose]
noncomputable def nb090AlphaDummy372 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy340 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy340 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_373`. -/
@[expose]
noncomputable def nb090AlphaDummy373 (A : Class) : Var :=
  (freshVar (((synC2nd)).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_374`. -/
@[expose]
noncomputable def nb090AlphaDummy374 (v : Var) : Var :=
  (freshVar (((synC2nd)).fv ∪ ((Class.cv v)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_375`. -/
@[expose]
noncomputable def nb090AlphaDummy375 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy373 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
          (Class.cv (nb090AlphaDummy373 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_376`. -/
@[expose]
noncomputable def nb090AlphaDummy376 (v : Var) : Var :=
  (freshVar (({(nb090AlphaDummy374 v)} : Finset Var) ∪
      ((synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_377`. -/
@[expose]
noncomputable def nb090AlphaDummy377 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy373 A)
            (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
              (Class.cv (nb090AlphaDummy373 A))))
          (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_378`. -/
@[expose]
noncomputable def nb090AlphaDummy378 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy373 A)
            (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
              (Class.cv (nb090AlphaDummy373 A))))
          (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_379`. -/
@[expose]
noncomputable def nb090AlphaDummy379 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq
          (Class.cab (nb090AlphaDummy374 v)
            (synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v))))
          (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_380`. -/
@[expose]
noncomputable def nb090AlphaDummy380 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq
          (Class.cab (nb090AlphaDummy374 v)
            (synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v))))
          (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_381`. -/
@[expose]
noncomputable def nb090AlphaDummy381 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy002 A))).fv ∪
      ((Class.cv (nb090AlphaDummy373 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_382`. -/
@[expose]
noncomputable def nb090AlphaDummy382 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy002 A))).fv ∪
      ((Class.cv (nb090AlphaDummy373 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_383`. -/
@[expose]
noncomputable def nb090AlphaDummy383 (v : Var) : Var :=
  (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_384`. -/
@[expose]
noncomputable def nb090AlphaDummy384 (v : Var) : Var :=
  (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_385`. -/
@[expose]
noncomputable def nb090AlphaDummy385 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCphi (Class.cv (nb090AlphaDummy382 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_386`. -/
@[expose]
noncomputable def nb090AlphaDummy386 (v : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy383 v)
            (synWrex (nb090AlphaDummy384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCphi (Class.cv (nb090AlphaDummy384 v)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy383 v)
            (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_387`. -/
@[expose]
noncomputable def nb090AlphaDummy387 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy381 A)
          (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
              (synCphi (Class.cv (nb090AlphaDummy382 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy381 A)
          (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
              (synCphi (Class.cv (nb090AlphaDummy382 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_388`. -/
@[expose]
noncomputable def nb090AlphaDummy388 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy383 v)
          (synWrex (nb090AlphaDummy384 v) (Class.cv v)
            (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
              (synCphi (Class.cv (nb090AlphaDummy384 v))))))).fv ∪
      ((Class.cab (nb090AlphaDummy383 v) (synWrex (nb090AlphaDummy384 v) (Class.cv v)
            (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
              (synCphi (Class.cv (nb090AlphaDummy384 v))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_389`. -/
@[expose]
noncomputable def nb090AlphaDummy389 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy382 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_390`. -/
@[expose]
noncomputable def nb090AlphaDummy390 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy382 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_391`. -/
@[expose]
noncomputable def nb090AlphaDummy391 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy384 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_392`. -/
@[expose]
noncomputable def nb090AlphaDummy392 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy384 v))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_393`. -/
@[expose]
noncomputable def nb090AlphaDummy393 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy389 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy389 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy389 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_394`. -/
@[expose]
noncomputable def nb090AlphaDummy394 (v : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy391 v)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy391 v)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy391 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_395`. -/
@[expose]
noncomputable def nb090AlphaDummy395 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_396`. -/
@[expose]
noncomputable def nb090AlphaDummy396 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_397`. -/
@[expose]
noncomputable def nb090AlphaDummy397 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_398`. -/
@[expose]
noncomputable def nb090AlphaDummy398 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_399`. -/
@[expose]
noncomputable def nb090AlphaDummy399 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_400`. -/
@[expose]
noncomputable def nb090AlphaDummy400 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_401`. -/
@[expose]
noncomputable def nb090AlphaDummy401 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy396 A))
          (Class.cv (nb090AlphaDummy397 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy396 A)) (Class.cv (nb090AlphaDummy397 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_402`. -/
@[expose]
noncomputable def nb090AlphaDummy402 (v : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy399 v))
          (Class.cv (nb090AlphaDummy400 v)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy399 v)) (Class.cv (nb090AlphaDummy400 v)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_403`. -/
@[expose]
noncomputable def nb090AlphaDummy403 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy396 A))).fv ∪
      ((Class.cv (nb090AlphaDummy397 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_404`. -/
@[expose]
noncomputable def nb090AlphaDummy404 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy399 v))).fv ∪
      ((Class.cv (nb090AlphaDummy400 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_405`. -/
@[expose]
noncomputable def nb090AlphaDummy405 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy396 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy397 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_406`. -/
@[expose]
noncomputable def nb090AlphaDummy406 (v : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy399 v)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy400 v)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_407`. -/
@[expose]
noncomputable def nb090AlphaDummy407 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy396 A))).fv ∪
      ((Class.cv (nb090AlphaDummy396 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_408`. -/
@[expose]
noncomputable def nb090AlphaDummy408 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy399 v))).fv ∪
      ((Class.cv (nb090AlphaDummy399 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_409`. -/
@[expose]
noncomputable def nb090AlphaDummy409 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy397 A))).fv ∪
      ((Class.cv (nb090AlphaDummy397 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_410`. -/
@[expose]
noncomputable def nb090AlphaDummy410 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy400 v))).fv ∪
      ((Class.cv (nb090AlphaDummy400 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_411`. -/
@[expose]
noncomputable def nb090AlphaDummy411 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy381 A)
          (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy381 A)
          (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_412`. -/
@[expose]
noncomputable def nb090AlphaDummy412 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy383 v)
          (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
            (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
              (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy383 v)
          (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
            (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
              (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_413`. -/
@[expose]
noncomputable def nb090AlphaDummy413 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy382 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_414`. -/
@[expose]
noncomputable def nb090AlphaDummy414 (v : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy384 v))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_415`. -/
@[expose]
noncomputable def nb090AlphaDummy415 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy382 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy382 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_416`. -/
@[expose]
noncomputable def nb090AlphaDummy416 (v : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy384 v)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy384 v)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_417`. -/
@[expose]
noncomputable def nb090AlphaDummy417 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy375 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_418`. -/
@[expose]
noncomputable def nb090AlphaDummy418 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy376 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_419`. -/
@[expose]
noncomputable def nb090AlphaDummy419 (A : Class) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))) (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_420`. -/
@[expose]
noncomputable def nb090AlphaDummy420 (h : Var) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
          (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
          (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_421`. -/
@[expose]
noncomputable def nb090AlphaDummy421 (A : Class) : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
          (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A)))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_422`. -/
@[expose]
noncomputable def nb090AlphaDummy422 (h : Var) : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))).fv ∪
      ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_423`. -/
@[expose]
noncomputable def nb090AlphaDummy423 (A : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_424`. -/
@[expose]
noncomputable def nb090AlphaDummy424 (A : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_425`. -/
@[expose]
noncomputable def nb090AlphaDummy425 (A : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_426`. -/
@[expose]
noncomputable def nb090AlphaDummy426 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_427`. -/
@[expose]
noncomputable def nb090AlphaDummy427 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_428`. -/
@[expose]
noncomputable def nb090AlphaDummy428 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_429`. -/
@[expose]
noncomputable def nb090AlphaDummy429 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy423 A)} : Finset Var) ∪
        ({(nb090AlphaDummy424 A)} : Finset Var) ∪ ((synWex (nb090AlphaDummy425 A) (synWa
            (synWbr (Class.cv (nb090AlphaDummy423 A))
              (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))
              (Class.cv (nb090AlphaDummy425 A)))
            (synWbr (Class.cv (nb090AlphaDummy425 A))
              (synCcnv (Class.cv (nb090AlphaDummy000 A)))
              (Class.cv (nb090AlphaDummy424 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_430`. -/
@[expose]
noncomputable def nb090AlphaDummy430 (h : Var) : Var :=
  (freshVar (({(nb090AlphaDummy426 h)} : Finset Var) ∪
        ({(nb090AlphaDummy427 h)} : Finset Var) ∪ ((synWex (nb090AlphaDummy428 h) (synWa
            (synWbr (Class.cv (nb090AlphaDummy426 h))
              (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb090AlphaDummy428 h)))
            (synWbr (Class.cv (nb090AlphaDummy428 h)) (synCcnv (Class.cv h))
              (Class.cv (nb090AlphaDummy427 h)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_431`. -/
@[expose]
noncomputable def nb090AlphaDummy431 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy423 A))).fv ∪
      ((Class.cv (nb090AlphaDummy424 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_432`. -/
@[expose]
noncomputable def nb090AlphaDummy432 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy423 A))).fv ∪
      ((Class.cv (nb090AlphaDummy424 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_433`. -/
@[expose]
noncomputable def nb090AlphaDummy433 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy426 h))).fv ∪
      ((Class.cv (nb090AlphaDummy427 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_434`. -/
@[expose]
noncomputable def nb090AlphaDummy434 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy426 h))).fv ∪
      ((Class.cv (nb090AlphaDummy427 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_435`. -/
@[expose]
noncomputable def nb090AlphaDummy435 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCphi (Class.cv (nb090AlphaDummy432 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_436`. -/
@[expose]
noncomputable def nb090AlphaDummy436 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCphi (Class.cv (nb090AlphaDummy434 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_437`. -/
@[expose]
noncomputable def nb090AlphaDummy437 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy431 A)
          (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
              (synCphi (Class.cv (nb090AlphaDummy432 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy431 A)
          (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
              (synCphi (Class.cv (nb090AlphaDummy432 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_438`. -/
@[expose]
noncomputable def nb090AlphaDummy438 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy433 h)
          (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
              (synCphi (Class.cv (nb090AlphaDummy434 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy433 h)
          (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
              (synCphi (Class.cv (nb090AlphaDummy434 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_439`. -/
@[expose]
noncomputable def nb090AlphaDummy439 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy432 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_440`. -/
@[expose]
noncomputable def nb090AlphaDummy440 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy432 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_441`. -/
@[expose]
noncomputable def nb090AlphaDummy441 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy434 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_442`. -/
@[expose]
noncomputable def nb090AlphaDummy442 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy434 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_443`. -/
@[expose]
noncomputable def nb090AlphaDummy443 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy439 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy439 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy439 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_444`. -/
@[expose]
noncomputable def nb090AlphaDummy444 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy441 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy441 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy441 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_445`. -/
@[expose]
noncomputable def nb090AlphaDummy445 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_446`. -/
@[expose]
noncomputable def nb090AlphaDummy446 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_447`. -/
@[expose]
noncomputable def nb090AlphaDummy447 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_448`. -/
@[expose]
noncomputable def nb090AlphaDummy448 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_449`. -/
@[expose]
noncomputable def nb090AlphaDummy449 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_450`. -/
@[expose]
noncomputable def nb090AlphaDummy450 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_451`. -/
@[expose]
noncomputable def nb090AlphaDummy451 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy446 A))
          (Class.cv (nb090AlphaDummy447 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy446 A)) (Class.cv (nb090AlphaDummy447 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_452`. -/
@[expose]
noncomputable def nb090AlphaDummy452 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy449 h))
          (Class.cv (nb090AlphaDummy450 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy449 h)) (Class.cv (nb090AlphaDummy450 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_453`. -/
@[expose]
noncomputable def nb090AlphaDummy453 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy446 A))).fv ∪
      ((Class.cv (nb090AlphaDummy447 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_454`. -/
@[expose]
noncomputable def nb090AlphaDummy454 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy449 h))).fv ∪
      ((Class.cv (nb090AlphaDummy450 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_455`. -/
@[expose]
noncomputable def nb090AlphaDummy455 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy446 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy447 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_456`. -/
@[expose]
noncomputable def nb090AlphaDummy456 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy449 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy450 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_457`. -/
@[expose]
noncomputable def nb090AlphaDummy457 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy446 A))).fv ∪
      ((Class.cv (nb090AlphaDummy446 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_458`. -/
@[expose]
noncomputable def nb090AlphaDummy458 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy449 h))).fv ∪
      ((Class.cv (nb090AlphaDummy449 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_459`. -/
@[expose]
noncomputable def nb090AlphaDummy459 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy447 A))).fv ∪
      ((Class.cv (nb090AlphaDummy447 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_460`. -/
@[expose]
noncomputable def nb090AlphaDummy460 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy450 h))).fv ∪
      ((Class.cv (nb090AlphaDummy450 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_461`. -/
@[expose]
noncomputable def nb090AlphaDummy461 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy431 A)
          (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy431 A)
          (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_462`. -/
@[expose]
noncomputable def nb090AlphaDummy462 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy433 h)
          (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy433 h)
          (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_463`. -/
@[expose]
noncomputable def nb090AlphaDummy463 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy432 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_464`. -/
@[expose]
noncomputable def nb090AlphaDummy464 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy434 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_465`. -/
@[expose]
noncomputable def nb090AlphaDummy465 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy432 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy432 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_466`. -/
@[expose]
noncomputable def nb090AlphaDummy466 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy434 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy434 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_467`. -/
@[expose]
noncomputable def nb090AlphaDummy467 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy423 A))).fv ∪
      ((Class.cv (nb090AlphaDummy425 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_468`. -/
@[expose]
noncomputable def nb090AlphaDummy468 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy423 A))).fv ∪
      ((Class.cv (nb090AlphaDummy425 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_469`. -/
@[expose]
noncomputable def nb090AlphaDummy469 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy426 h))).fv ∪
      ((Class.cv (nb090AlphaDummy428 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_470`. -/
@[expose]
noncomputable def nb090AlphaDummy470 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy426 h))).fv ∪
      ((Class.cv (nb090AlphaDummy428 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_471`. -/
@[expose]
noncomputable def nb090AlphaDummy471 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCphi (Class.cv (nb090AlphaDummy468 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_472`. -/
@[expose]
noncomputable def nb090AlphaDummy472 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCphi (Class.cv (nb090AlphaDummy470 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_473`. -/
@[expose]
noncomputable def nb090AlphaDummy473 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy467 A)
          (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
              (synCphi (Class.cv (nb090AlphaDummy468 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy467 A)
          (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
              (synCphi (Class.cv (nb090AlphaDummy468 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_474`. -/
@[expose]
noncomputable def nb090AlphaDummy474 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy469 h)
          (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
              (synCphi (Class.cv (nb090AlphaDummy470 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy469 h)
          (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
              (synCphi (Class.cv (nb090AlphaDummy470 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_475`. -/
@[expose]
noncomputable def nb090AlphaDummy475 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy468 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_476`. -/
@[expose]
noncomputable def nb090AlphaDummy476 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy468 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_477`. -/
@[expose]
noncomputable def nb090AlphaDummy477 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy470 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_478`. -/
@[expose]
noncomputable def nb090AlphaDummy478 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy470 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_479`. -/
@[expose]
noncomputable def nb090AlphaDummy479 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy475 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy475 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy475 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_480`. -/
@[expose]
noncomputable def nb090AlphaDummy480 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy477 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy477 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy477 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_481`. -/
@[expose]
noncomputable def nb090AlphaDummy481 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_482`. -/
@[expose]
noncomputable def nb090AlphaDummy482 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_483`. -/
@[expose]
noncomputable def nb090AlphaDummy483 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_484`. -/
@[expose]
noncomputable def nb090AlphaDummy484 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_485`. -/
@[expose]
noncomputable def nb090AlphaDummy485 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_486`. -/
@[expose]
noncomputable def nb090AlphaDummy486 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_487`. -/
@[expose]
noncomputable def nb090AlphaDummy487 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy482 A))
          (Class.cv (nb090AlphaDummy483 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy482 A)) (Class.cv (nb090AlphaDummy483 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_488`. -/
@[expose]
noncomputable def nb090AlphaDummy488 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy485 h))
          (Class.cv (nb090AlphaDummy486 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy485 h)) (Class.cv (nb090AlphaDummy486 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_489`. -/
@[expose]
noncomputable def nb090AlphaDummy489 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy482 A))).fv ∪
      ((Class.cv (nb090AlphaDummy483 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_490`. -/
@[expose]
noncomputable def nb090AlphaDummy490 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy485 h))).fv ∪
      ((Class.cv (nb090AlphaDummy486 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_491`. -/
@[expose]
noncomputable def nb090AlphaDummy491 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy482 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy483 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_492`. -/
@[expose]
noncomputable def nb090AlphaDummy492 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy485 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy486 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_493`. -/
@[expose]
noncomputable def nb090AlphaDummy493 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy482 A))).fv ∪
      ((Class.cv (nb090AlphaDummy482 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_494`. -/
@[expose]
noncomputable def nb090AlphaDummy494 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy485 h))).fv ∪
      ((Class.cv (nb090AlphaDummy485 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_495`. -/
@[expose]
noncomputable def nb090AlphaDummy495 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy483 A))).fv ∪
      ((Class.cv (nb090AlphaDummy483 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_496`. -/
@[expose]
noncomputable def nb090AlphaDummy496 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy486 h))).fv ∪
      ((Class.cv (nb090AlphaDummy486 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_497`. -/
@[expose]
noncomputable def nb090AlphaDummy497 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy467 A)
          (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy467 A)
          (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_498`. -/
@[expose]
noncomputable def nb090AlphaDummy498 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy469 h)
          (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy469 h)
          (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_499`. -/
@[expose]
noncomputable def nb090AlphaDummy499 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy468 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_500`. -/
@[expose]
noncomputable def nb090AlphaDummy500 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy470 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_501`. -/
@[expose]
noncomputable def nb090AlphaDummy501 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy468 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy468 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_502`. -/
@[expose]
noncomputable def nb090AlphaDummy502 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy470 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy470 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_503`. -/
@[expose]
noncomputable def nb090AlphaDummy503 (A : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_504`. -/
@[expose]
noncomputable def nb090AlphaDummy504 (A : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_505`. -/
@[expose]
noncomputable def nb090AlphaDummy505 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_506`. -/
@[expose]
noncomputable def nb090AlphaDummy506 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_507`. -/
@[expose]
noncomputable def nb090AlphaDummy507 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy503 A)} : Finset Var) ∪
        ({(nb090AlphaDummy504 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy504 A))
          (synCcnv (Class.cv (nb090AlphaDummy000 A)))
          (Class.cv (nb090AlphaDummy503 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_508`. -/
@[expose]
noncomputable def nb090AlphaDummy508 (h : Var) : Var :=
  (freshVar (({(nb090AlphaDummy505 h)} : Finset Var) ∪
        ({(nb090AlphaDummy506 h)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy506 h)) (synCcnv (Class.cv h))
          (Class.cv (nb090AlphaDummy505 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_509`. -/
@[expose]
noncomputable def nb090AlphaDummy509 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy503 A))).fv ∪
      ((Class.cv (nb090AlphaDummy504 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_510`. -/
@[expose]
noncomputable def nb090AlphaDummy510 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy503 A))).fv ∪
      ((Class.cv (nb090AlphaDummy504 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_511`. -/
@[expose]
noncomputable def nb090AlphaDummy511 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy505 h))).fv ∪
      ((Class.cv (nb090AlphaDummy506 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_512`. -/
@[expose]
noncomputable def nb090AlphaDummy512 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy505 h))).fv ∪
      ((Class.cv (nb090AlphaDummy506 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_513`. -/
@[expose]
noncomputable def nb090AlphaDummy513 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCphi (Class.cv (nb090AlphaDummy510 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_514`. -/
@[expose]
noncomputable def nb090AlphaDummy514 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCphi (Class.cv (nb090AlphaDummy512 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_515`. -/
@[expose]
noncomputable def nb090AlphaDummy515 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy509 A)
          (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
              (synCphi (Class.cv (nb090AlphaDummy510 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy509 A)
          (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
              (synCphi (Class.cv (nb090AlphaDummy510 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_516`. -/
@[expose]
noncomputable def nb090AlphaDummy516 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy511 h)
          (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
              (synCphi (Class.cv (nb090AlphaDummy512 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy511 h)
          (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
              (synCphi (Class.cv (nb090AlphaDummy512 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_517`. -/
@[expose]
noncomputable def nb090AlphaDummy517 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy510 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_518`. -/
@[expose]
noncomputable def nb090AlphaDummy518 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy510 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_519`. -/
@[expose]
noncomputable def nb090AlphaDummy519 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy512 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_520`. -/
@[expose]
noncomputable def nb090AlphaDummy520 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy512 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_521`. -/
@[expose]
noncomputable def nb090AlphaDummy521 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy517 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy517 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy517 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_522`. -/
@[expose]
noncomputable def nb090AlphaDummy522 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy519 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy519 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy519 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_523`. -/
@[expose]
noncomputable def nb090AlphaDummy523 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_524`. -/
@[expose]
noncomputable def nb090AlphaDummy524 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_525`. -/
@[expose]
noncomputable def nb090AlphaDummy525 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_526`. -/
@[expose]
noncomputable def nb090AlphaDummy526 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_527`. -/
@[expose]
noncomputable def nb090AlphaDummy527 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_528`. -/
@[expose]
noncomputable def nb090AlphaDummy528 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_529`. -/
@[expose]
noncomputable def nb090AlphaDummy529 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy524 A))
          (Class.cv (nb090AlphaDummy525 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy524 A)) (Class.cv (nb090AlphaDummy525 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_530`. -/
@[expose]
noncomputable def nb090AlphaDummy530 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy527 h))
          (Class.cv (nb090AlphaDummy528 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy527 h)) (Class.cv (nb090AlphaDummy528 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_531`. -/
@[expose]
noncomputable def nb090AlphaDummy531 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy524 A))).fv ∪
      ((Class.cv (nb090AlphaDummy525 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_532`. -/
@[expose]
noncomputable def nb090AlphaDummy532 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy527 h))).fv ∪
      ((Class.cv (nb090AlphaDummy528 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_533`. -/
@[expose]
noncomputable def nb090AlphaDummy533 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy524 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy525 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_534`. -/
@[expose]
noncomputable def nb090AlphaDummy534 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy527 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy528 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_535`. -/
@[expose]
noncomputable def nb090AlphaDummy535 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy524 A))).fv ∪
      ((Class.cv (nb090AlphaDummy524 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_536`. -/
@[expose]
noncomputable def nb090AlphaDummy536 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy527 h))).fv ∪
      ((Class.cv (nb090AlphaDummy527 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_537`. -/
@[expose]
noncomputable def nb090AlphaDummy537 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy525 A))).fv ∪
      ((Class.cv (nb090AlphaDummy525 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_538`. -/
@[expose]
noncomputable def nb090AlphaDummy538 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy528 h))).fv ∪
      ((Class.cv (nb090AlphaDummy528 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_539`. -/
@[expose]
noncomputable def nb090AlphaDummy539 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy509 A)
          (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy509 A)
          (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_540`. -/
@[expose]
noncomputable def nb090AlphaDummy540 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy511 h)
          (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy511 h)
          (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_541`. -/
@[expose]
noncomputable def nb090AlphaDummy541 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy510 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_542`. -/
@[expose]
noncomputable def nb090AlphaDummy542 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy512 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_543`. -/
@[expose]
noncomputable def nb090AlphaDummy543 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy510 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy510 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_544`. -/
@[expose]
noncomputable def nb090AlphaDummy544 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy512 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy512 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_545`. -/
@[expose]
noncomputable def nb090AlphaDummy545 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy504 A))).fv ∪
      ((Class.cv (nb090AlphaDummy503 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_546`. -/
@[expose]
noncomputable def nb090AlphaDummy546 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy504 A))).fv ∪
      ((Class.cv (nb090AlphaDummy503 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_547`. -/
@[expose]
noncomputable def nb090AlphaDummy547 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy506 h))).fv ∪
      ((Class.cv (nb090AlphaDummy505 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_548`. -/
@[expose]
noncomputable def nb090AlphaDummy548 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy506 h))).fv ∪
      ((Class.cv (nb090AlphaDummy505 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_549`. -/
@[expose]
noncomputable def nb090AlphaDummy549 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCphi (Class.cv (nb090AlphaDummy546 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_550`. -/
@[expose]
noncomputable def nb090AlphaDummy550 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCphi (Class.cv (nb090AlphaDummy548 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_551`. -/
@[expose]
noncomputable def nb090AlphaDummy551 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy545 A)
          (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
              (synCphi (Class.cv (nb090AlphaDummy546 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy545 A)
          (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
              (synCphi (Class.cv (nb090AlphaDummy546 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_552`. -/
@[expose]
noncomputable def nb090AlphaDummy552 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy547 h)
          (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
              (synCphi (Class.cv (nb090AlphaDummy548 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy547 h)
          (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
              (synCphi (Class.cv (nb090AlphaDummy548 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_553`. -/
@[expose]
noncomputable def nb090AlphaDummy553 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy546 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_554`. -/
@[expose]
noncomputable def nb090AlphaDummy554 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy546 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_555`. -/
@[expose]
noncomputable def nb090AlphaDummy555 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy548 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_556`. -/
@[expose]
noncomputable def nb090AlphaDummy556 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy548 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_557`. -/
@[expose]
noncomputable def nb090AlphaDummy557 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy553 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy553 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy553 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_558`. -/
@[expose]
noncomputable def nb090AlphaDummy558 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy555 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy555 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy555 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_559`. -/
@[expose]
noncomputable def nb090AlphaDummy559 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_560`. -/
@[expose]
noncomputable def nb090AlphaDummy560 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_561`. -/
@[expose]
noncomputable def nb090AlphaDummy561 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_562`. -/
@[expose]
noncomputable def nb090AlphaDummy562 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_563`. -/
@[expose]
noncomputable def nb090AlphaDummy563 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_564`. -/
@[expose]
noncomputable def nb090AlphaDummy564 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_565`. -/
@[expose]
noncomputable def nb090AlphaDummy565 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy560 A))
          (Class.cv (nb090AlphaDummy561 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy560 A)) (Class.cv (nb090AlphaDummy561 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_566`. -/
@[expose]
noncomputable def nb090AlphaDummy566 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy563 h))
          (Class.cv (nb090AlphaDummy564 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy563 h)) (Class.cv (nb090AlphaDummy564 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_567`. -/
@[expose]
noncomputable def nb090AlphaDummy567 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy560 A))).fv ∪
      ((Class.cv (nb090AlphaDummy561 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_568`. -/
@[expose]
noncomputable def nb090AlphaDummy568 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy563 h))).fv ∪
      ((Class.cv (nb090AlphaDummy564 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_569`. -/
@[expose]
noncomputable def nb090AlphaDummy569 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy560 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy561 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_570`. -/
@[expose]
noncomputable def nb090AlphaDummy570 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy563 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy564 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_571`. -/
@[expose]
noncomputable def nb090AlphaDummy571 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy560 A))).fv ∪
      ((Class.cv (nb090AlphaDummy560 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_572`. -/
@[expose]
noncomputable def nb090AlphaDummy572 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy563 h))).fv ∪
      ((Class.cv (nb090AlphaDummy563 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_573`. -/
@[expose]
noncomputable def nb090AlphaDummy573 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy561 A))).fv ∪
      ((Class.cv (nb090AlphaDummy561 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_574`. -/
@[expose]
noncomputable def nb090AlphaDummy574 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy564 h))).fv ∪
      ((Class.cv (nb090AlphaDummy564 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_575`. -/
@[expose]
noncomputable def nb090AlphaDummy575 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy545 A)
          (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy545 A)
          (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_576`. -/
@[expose]
noncomputable def nb090AlphaDummy576 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy547 h)
          (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy547 h)
          (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_577`. -/
@[expose]
noncomputable def nb090AlphaDummy577 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy546 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_578`. -/
@[expose]
noncomputable def nb090AlphaDummy578 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy548 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_579`. -/
@[expose]
noncomputable def nb090AlphaDummy579 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy546 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy546 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_580`. -/
@[expose]
noncomputable def nb090AlphaDummy580 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy548 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy548 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_581`. -/
@[expose]
noncomputable def nb090AlphaDummy581 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy425 A))).fv ∪
      ((Class.cv (nb090AlphaDummy424 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_582`. -/
@[expose]
noncomputable def nb090AlphaDummy582 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy425 A))).fv ∪
      ((Class.cv (nb090AlphaDummy424 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_583`. -/
@[expose]
noncomputable def nb090AlphaDummy583 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy428 h))).fv ∪
      ((Class.cv (nb090AlphaDummy427 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_584`. -/
@[expose]
noncomputable def nb090AlphaDummy584 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy428 h))).fv ∪
      ((Class.cv (nb090AlphaDummy427 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_585`. -/
@[expose]
noncomputable def nb090AlphaDummy585 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCphi (Class.cv (nb090AlphaDummy582 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_586`. -/
@[expose]
noncomputable def nb090AlphaDummy586 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCphi (Class.cv (nb090AlphaDummy584 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_587`. -/
@[expose]
noncomputable def nb090AlphaDummy587 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy581 A)
          (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
              (synCphi (Class.cv (nb090AlphaDummy582 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy581 A)
          (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
              (synCphi (Class.cv (nb090AlphaDummy582 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_588`. -/
@[expose]
noncomputable def nb090AlphaDummy588 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy583 h)
          (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
              (synCphi (Class.cv (nb090AlphaDummy584 h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy583 h)
          (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
              (synCphi (Class.cv (nb090AlphaDummy584 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_589`. -/
@[expose]
noncomputable def nb090AlphaDummy589 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy582 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_590`. -/
@[expose]
noncomputable def nb090AlphaDummy590 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy582 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_591`. -/
@[expose]
noncomputable def nb090AlphaDummy591 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy584 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_592`. -/
@[expose]
noncomputable def nb090AlphaDummy592 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy584 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_593`. -/
@[expose]
noncomputable def nb090AlphaDummy593 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy589 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy589 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy589 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_594`. -/
@[expose]
noncomputable def nb090AlphaDummy594 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy591 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy591 h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy591 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_595`. -/
@[expose]
noncomputable def nb090AlphaDummy595 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_596`. -/
@[expose]
noncomputable def nb090AlphaDummy596 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_597`. -/
@[expose]
noncomputable def nb090AlphaDummy597 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_598`. -/
@[expose]
noncomputable def nb090AlphaDummy598 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_599`. -/
@[expose]
noncomputable def nb090AlphaDummy599 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_600`. -/
@[expose]
noncomputable def nb090AlphaDummy600 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_601`. -/
@[expose]
noncomputable def nb090AlphaDummy601 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy596 A))
          (Class.cv (nb090AlphaDummy597 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy596 A)) (Class.cv (nb090AlphaDummy597 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_602`. -/
@[expose]
noncomputable def nb090AlphaDummy602 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy599 h))
          (Class.cv (nb090AlphaDummy600 h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy599 h)) (Class.cv (nb090AlphaDummy600 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_603`. -/
@[expose]
noncomputable def nb090AlphaDummy603 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy596 A))).fv ∪
      ((Class.cv (nb090AlphaDummy597 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_604`. -/
@[expose]
noncomputable def nb090AlphaDummy604 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy599 h))).fv ∪
      ((Class.cv (nb090AlphaDummy600 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_605`. -/
@[expose]
noncomputable def nb090AlphaDummy605 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy596 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy597 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_606`. -/
@[expose]
noncomputable def nb090AlphaDummy606 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy599 h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy600 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_607`. -/
@[expose]
noncomputable def nb090AlphaDummy607 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy596 A))).fv ∪
      ((Class.cv (nb090AlphaDummy596 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_608`. -/
@[expose]
noncomputable def nb090AlphaDummy608 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy599 h))).fv ∪
      ((Class.cv (nb090AlphaDummy599 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_609`. -/
@[expose]
noncomputable def nb090AlphaDummy609 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy597 A))).fv ∪
      ((Class.cv (nb090AlphaDummy597 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_610`. -/
@[expose]
noncomputable def nb090AlphaDummy610 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy600 h))).fv ∪
      ((Class.cv (nb090AlphaDummy600 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_611`. -/
@[expose]
noncomputable def nb090AlphaDummy611 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy581 A)
          (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy581 A)
          (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_612`. -/
@[expose]
noncomputable def nb090AlphaDummy612 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy583 h)
          (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy583 h)
          (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
            (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_613`. -/
@[expose]
noncomputable def nb090AlphaDummy613 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy582 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_614`. -/
@[expose]
noncomputable def nb090AlphaDummy614 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy584 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_615`. -/
@[expose]
noncomputable def nb090AlphaDummy615 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy582 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy582 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_616`. -/
@[expose]
noncomputable def nb090AlphaDummy616 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy584 h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy584 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_617`. -/
@[expose]
noncomputable def nb090AlphaDummy617 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy041 A))).fv ∪
      ((Class.cv (nb090AlphaDummy042 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_618`. -/
@[expose]
noncomputable def nb090AlphaDummy618 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy041 A))).fv ∪
      ((Class.cv (nb090AlphaDummy042 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_619`. -/
@[expose]
noncomputable def nb090AlphaDummy619 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy044 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_620`. -/
@[expose]
noncomputable def nb090AlphaDummy620 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy044 v u h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_621`. -/
@[expose]
noncomputable def nb090AlphaDummy621 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCphi (Class.cv (nb090AlphaDummy618 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_622`. -/
@[expose]
noncomputable def nb090AlphaDummy622 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy619 v u h)
            (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCphi (Class.cv (nb090AlphaDummy620 v u h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_623`. -/
@[expose]
noncomputable def nb090AlphaDummy623 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy617 A)
          (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
              (synCphi (Class.cv (nb090AlphaDummy618 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy617 A)
          (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
              (synCphi (Class.cv (nb090AlphaDummy618 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_624`. -/
@[expose]
noncomputable def nb090AlphaDummy624 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy619 v u h)
          (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy043 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
              (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy619 v u h)
          (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy043 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
              (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_625`. -/
@[expose]
noncomputable def nb090AlphaDummy625 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy618 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_626`. -/
@[expose]
noncomputable def nb090AlphaDummy626 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy618 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_627`. -/
@[expose]
noncomputable def nb090AlphaDummy627 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy620 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_628`. -/
@[expose]
noncomputable def nb090AlphaDummy628 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy620 v u h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_629`. -/
@[expose]
noncomputable def nb090AlphaDummy629 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy625 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy625 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy625 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_630`. -/
@[expose]
noncomputable def nb090AlphaDummy630 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy627 v u h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy627 v u h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy627 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_631`. -/
@[expose]
noncomputable def nb090AlphaDummy631 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_632`. -/
@[expose]
noncomputable def nb090AlphaDummy632 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_633`. -/
@[expose]
noncomputable def nb090AlphaDummy633 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_634`. -/
@[expose]
noncomputable def nb090AlphaDummy634 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_635`. -/
@[expose]
noncomputable def nb090AlphaDummy635 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_636`. -/
@[expose]
noncomputable def nb090AlphaDummy636 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_637`. -/
@[expose]
noncomputable def nb090AlphaDummy637 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy632 A))
          (Class.cv (nb090AlphaDummy633 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy632 A)) (Class.cv (nb090AlphaDummy633 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_638`. -/
@[expose]
noncomputable def nb090AlphaDummy638 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy635 v u h))
          (Class.cv (nb090AlphaDummy636 v u h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy635 v u h))
          (Class.cv (nb090AlphaDummy636 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_639`. -/
@[expose]
noncomputable def nb090AlphaDummy639 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy632 A))).fv ∪
      ((Class.cv (nb090AlphaDummy633 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_640`. -/
@[expose]
noncomputable def nb090AlphaDummy640 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy636 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_641`. -/
@[expose]
noncomputable def nb090AlphaDummy641 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy632 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy633 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_642`. -/
@[expose]
noncomputable def nb090AlphaDummy642 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy635 v u h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy636 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_643`. -/
@[expose]
noncomputable def nb090AlphaDummy643 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy632 A))).fv ∪
      ((Class.cv (nb090AlphaDummy632 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_644`. -/
@[expose]
noncomputable def nb090AlphaDummy644 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy635 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_645`. -/
@[expose]
noncomputable def nb090AlphaDummy645 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy633 A))).fv ∪
      ((Class.cv (nb090AlphaDummy633 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_646`. -/
@[expose]
noncomputable def nb090AlphaDummy646 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy636 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy636 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_647`. -/
@[expose]
noncomputable def nb090AlphaDummy647 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy617 A)
          (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy617 A)
          (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_648`. -/
@[expose]
noncomputable def nb090AlphaDummy648 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy619 v u h)
          (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy044 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy619 v u h)
          (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy044 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_649`. -/
@[expose]
noncomputable def nb090AlphaDummy649 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy618 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_650`. -/
@[expose]
noncomputable def nb090AlphaDummy650 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy620 v u h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_651`. -/
@[expose]
noncomputable def nb090AlphaDummy651 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy618 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy618 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_652`. -/
@[expose]
noncomputable def nb090AlphaDummy652 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy620 v u h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy620 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_653`. -/
@[expose]
noncomputable def nb090AlphaDummy653 (A : Class) : Var :=
  (freshVar (((synC1st)).fv ∪ ((Class.cv (nb090AlphaDummy001 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_654`. -/
@[expose]
noncomputable def nb090AlphaDummy654 (u : Var) : Var :=
  (freshVar (((synC1st)).fv ∪ ((Class.cv u)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_655`. -/
@[expose]
noncomputable def nb090AlphaDummy655 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy653 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
          (Class.cv (nb090AlphaDummy653 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_656`. -/
@[expose]
noncomputable def nb090AlphaDummy656 (u : Var) : Var :=
  (freshVar (({(nb090AlphaDummy654 u)} : Finset Var) ∪
      ((synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_657`. -/
@[expose]
noncomputable def nb090AlphaDummy657 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy653 A)
            (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
              (Class.cv (nb090AlphaDummy653 A))))
          (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_658`. -/
@[expose]
noncomputable def nb090AlphaDummy658 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy653 A)
            (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
              (Class.cv (nb090AlphaDummy653 A))))
          (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_659`. -/
@[expose]
noncomputable def nb090AlphaDummy659 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq
          (Class.cab (nb090AlphaDummy654 u)
            (synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u))))
          (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_660`. -/
@[expose]
noncomputable def nb090AlphaDummy660 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq
          (Class.cab (nb090AlphaDummy654 u)
            (synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u))))
          (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_661`. -/
@[expose]
noncomputable def nb090AlphaDummy661 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy001 A))).fv ∪
      ((Class.cv (nb090AlphaDummy653 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_662`. -/
@[expose]
noncomputable def nb090AlphaDummy662 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy001 A))).fv ∪
      ((Class.cv (nb090AlphaDummy653 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_663`. -/
@[expose]
noncomputable def nb090AlphaDummy663 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_664`. -/
@[expose]
noncomputable def nb090AlphaDummy664 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_665`. -/
@[expose]
noncomputable def nb090AlphaDummy665 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCphi (Class.cv (nb090AlphaDummy662 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_666`. -/
@[expose]
noncomputable def nb090AlphaDummy666 (u : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy663 u)
            (synWrex (nb090AlphaDummy664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCphi (Class.cv (nb090AlphaDummy664 u)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy663 u)
            (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_667`. -/
@[expose]
noncomputable def nb090AlphaDummy667 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy661 A)
          (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
              (synCphi (Class.cv (nb090AlphaDummy662 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy661 A)
          (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
              (synCphi (Class.cv (nb090AlphaDummy662 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_668`. -/
@[expose]
noncomputable def nb090AlphaDummy668 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy663 u)
          (synWrex (nb090AlphaDummy664 u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
              (synCphi (Class.cv (nb090AlphaDummy664 u))))))).fv ∪
      ((Class.cab (nb090AlphaDummy663 u) (synWrex (nb090AlphaDummy664 u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
              (synCphi (Class.cv (nb090AlphaDummy664 u))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_669`. -/
@[expose]
noncomputable def nb090AlphaDummy669 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy662 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_670`. -/
@[expose]
noncomputable def nb090AlphaDummy670 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy662 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_671`. -/
@[expose]
noncomputable def nb090AlphaDummy671 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy664 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_672`. -/
@[expose]
noncomputable def nb090AlphaDummy672 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy664 u))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_673`. -/
@[expose]
noncomputable def nb090AlphaDummy673 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy669 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy669 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy669 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_674`. -/
@[expose]
noncomputable def nb090AlphaDummy674 (u : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy671 u)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy671 u)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy671 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_675`. -/
@[expose]
noncomputable def nb090AlphaDummy675 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_676`. -/
@[expose]
noncomputable def nb090AlphaDummy676 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_677`. -/
@[expose]
noncomputable def nb090AlphaDummy677 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_678`. -/
@[expose]
noncomputable def nb090AlphaDummy678 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_679`. -/
@[expose]
noncomputable def nb090AlphaDummy679 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_680`. -/
@[expose]
noncomputable def nb090AlphaDummy680 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_681`. -/
@[expose]
noncomputable def nb090AlphaDummy681 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy676 A))
          (Class.cv (nb090AlphaDummy677 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy676 A)) (Class.cv (nb090AlphaDummy677 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_682`. -/
@[expose]
noncomputable def nb090AlphaDummy682 (u : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy679 u))
          (Class.cv (nb090AlphaDummy680 u)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy679 u)) (Class.cv (nb090AlphaDummy680 u)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_683`. -/
@[expose]
noncomputable def nb090AlphaDummy683 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy676 A))).fv ∪
      ((Class.cv (nb090AlphaDummy677 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_684`. -/
@[expose]
noncomputable def nb090AlphaDummy684 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy679 u))).fv ∪
      ((Class.cv (nb090AlphaDummy680 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_685`. -/
@[expose]
noncomputable def nb090AlphaDummy685 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy676 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy677 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_686`. -/
@[expose]
noncomputable def nb090AlphaDummy686 (u : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy679 u)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy680 u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_687`. -/
@[expose]
noncomputable def nb090AlphaDummy687 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy676 A))).fv ∪
      ((Class.cv (nb090AlphaDummy676 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_688`. -/
@[expose]
noncomputable def nb090AlphaDummy688 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy679 u))).fv ∪
      ((Class.cv (nb090AlphaDummy679 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_689`. -/
@[expose]
noncomputable def nb090AlphaDummy689 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy677 A))).fv ∪
      ((Class.cv (nb090AlphaDummy677 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_690`. -/
@[expose]
noncomputable def nb090AlphaDummy690 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy680 u))).fv ∪
      ((Class.cv (nb090AlphaDummy680 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_691`. -/
@[expose]
noncomputable def nb090AlphaDummy691 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy661 A)
          (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy661 A)
          (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_692`. -/
@[expose]
noncomputable def nb090AlphaDummy692 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy663 u)
          (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
            (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
              (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy663 u)
          (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
            (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
              (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_693`. -/
@[expose]
noncomputable def nb090AlphaDummy693 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy662 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_694`. -/
@[expose]
noncomputable def nb090AlphaDummy694 (u : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy664 u))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_695`. -/
@[expose]
noncomputable def nb090AlphaDummy695 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy662 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy662 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_696`. -/
@[expose]
noncomputable def nb090AlphaDummy696 (u : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy664 u)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy664 u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_697`. -/
@[expose]
noncomputable def nb090AlphaDummy697 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy655 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_698`. -/
@[expose]
noncomputable def nb090AlphaDummy698 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy656 u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_699`. -/
@[expose]
noncomputable def nb090AlphaDummy699 (A : Class) : Var :=
  (freshVar (((synCfv (Class.cv (nb090AlphaDummy000 A))
          (Class.cv (nb090AlphaDummy041 A)))).fv ∪
      ((synCfv (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy042 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_700`. -/
@[expose]
noncomputable def nb090AlphaDummy700 (A : Class) : Var :=
  (freshVar (((synCfv (Class.cv (nb090AlphaDummy000 A))
          (Class.cv (nb090AlphaDummy041 A)))).fv ∪
      ((synCfv (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy042 A)))).fv)
    1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_701`. -/
@[expose]
noncomputable def nb090AlphaDummy701 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
      ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_702`. -/
@[expose]
noncomputable def nb090AlphaDummy702 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
      ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_703`. -/
@[expose]
noncomputable def nb090AlphaDummy703 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy699 A)
            (synWrex (nb090AlphaDummy700 A) (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_704`. -/
@[expose]
noncomputable def nb090AlphaDummy704 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy701 v u h)
            (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_705`. -/
@[expose]
noncomputable def nb090AlphaDummy705 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
            (synCfv (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy041 A)))
            (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
              (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
            (synCfv (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy041 A)))
            (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
              (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_706`. -/
@[expose]
noncomputable def nb090AlphaDummy706 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
            (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
            (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
              (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
            (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
            (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
              (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_707`. -/
@[expose]
noncomputable def nb090AlphaDummy707 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪
      ((Class.cv (nb090AlphaDummy041 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_708`. -/
@[expose]
noncomputable def nb090AlphaDummy708 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy043 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_709`. -/
@[expose]
noncomputable def nb090AlphaDummy709 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy707 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
          (Class.cv (nb090AlphaDummy707 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_710`. -/
@[expose]
noncomputable def nb090AlphaDummy710 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (({(nb090AlphaDummy708 v u h)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
          (Class.cv (nb090AlphaDummy708 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_711`. -/
@[expose]
noncomputable def nb090AlphaDummy711 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy707 A) (synWbr (Class.cv (nb090AlphaDummy041 A))
              (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy707 A))))
          (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_712`. -/
@[expose]
noncomputable def nb090AlphaDummy712 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy707 A) (synWbr (Class.cv (nb090AlphaDummy041 A))
              (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy707 A))))
          (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_713`. -/
@[expose]
noncomputable def nb090AlphaDummy713 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
          (Class.cab (nb090AlphaDummy708 v u h)
            (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
              (Class.cv (nb090AlphaDummy708 v u h))))
          (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_714`. -/
@[expose]
noncomputable def nb090AlphaDummy714 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
          (Class.cab (nb090AlphaDummy708 v u h)
            (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
              (Class.cv (nb090AlphaDummy708 v u h))))
          (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_715`. -/
@[expose]
noncomputable def nb090AlphaDummy715 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy041 A))).fv ∪
      ((Class.cv (nb090AlphaDummy707 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_716`. -/
@[expose]
noncomputable def nb090AlphaDummy716 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy041 A))).fv ∪
      ((Class.cv (nb090AlphaDummy707 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_717`. -/
@[expose]
noncomputable def nb090AlphaDummy717 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy708 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_718`. -/
@[expose]
noncomputable def nb090AlphaDummy718 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy708 v u h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_719`. -/
@[expose]
noncomputable def nb090AlphaDummy719 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCphi (Class.cv (nb090AlphaDummy716 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_720`. -/
@[expose]
noncomputable def nb090AlphaDummy720 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy717 v u h)
            (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCphi (Class.cv (nb090AlphaDummy718 v u h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy708 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_721`. -/
@[expose]
noncomputable def nb090AlphaDummy721 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy715 A)
          (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
              (synCphi (Class.cv (nb090AlphaDummy716 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy715 A)
          (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
              (synCphi (Class.cv (nb090AlphaDummy716 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_722`. -/
@[expose]
noncomputable def nb090AlphaDummy722 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy717 v u h)
          (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy043 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
              (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy717 v u h)
          (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy043 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
              (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_723`. -/
@[expose]
noncomputable def nb090AlphaDummy723 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy716 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_724`. -/
@[expose]
noncomputable def nb090AlphaDummy724 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy716 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_725`. -/
@[expose]
noncomputable def nb090AlphaDummy725 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy718 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_726`. -/
@[expose]
noncomputable def nb090AlphaDummy726 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy718 v u h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_727`. -/
@[expose]
noncomputable def nb090AlphaDummy727 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy723 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy723 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy723 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_728`. -/
@[expose]
noncomputable def nb090AlphaDummy728 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy725 v u h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy725 v u h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy725 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_729`. -/
@[expose]
noncomputable def nb090AlphaDummy729 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_730`. -/
@[expose]
noncomputable def nb090AlphaDummy730 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_731`. -/
@[expose]
noncomputable def nb090AlphaDummy731 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_732`. -/
@[expose]
noncomputable def nb090AlphaDummy732 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_733`. -/
@[expose]
noncomputable def nb090AlphaDummy733 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_734`. -/
@[expose]
noncomputable def nb090AlphaDummy734 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_735`. -/
@[expose]
noncomputable def nb090AlphaDummy735 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy730 A))
          (Class.cv (nb090AlphaDummy731 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy730 A)) (Class.cv (nb090AlphaDummy731 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_736`. -/
@[expose]
noncomputable def nb090AlphaDummy736 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy733 v u h))
          (Class.cv (nb090AlphaDummy734 v u h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy733 v u h))
          (Class.cv (nb090AlphaDummy734 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_737`. -/
@[expose]
noncomputable def nb090AlphaDummy737 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy730 A))).fv ∪
      ((Class.cv (nb090AlphaDummy731 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_738`. -/
@[expose]
noncomputable def nb090AlphaDummy738 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy734 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_739`. -/
@[expose]
noncomputable def nb090AlphaDummy739 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy730 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy731 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_740`. -/
@[expose]
noncomputable def nb090AlphaDummy740 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy733 v u h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy734 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_741`. -/
@[expose]
noncomputable def nb090AlphaDummy741 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy730 A))).fv ∪
      ((Class.cv (nb090AlphaDummy730 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_742`. -/
@[expose]
noncomputable def nb090AlphaDummy742 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy733 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_743`. -/
@[expose]
noncomputable def nb090AlphaDummy743 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy731 A))).fv ∪
      ((Class.cv (nb090AlphaDummy731 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_744`. -/
@[expose]
noncomputable def nb090AlphaDummy744 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy734 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy734 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_745`. -/
@[expose]
noncomputable def nb090AlphaDummy745 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy715 A)
          (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy715 A)
          (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_746`. -/
@[expose]
noncomputable def nb090AlphaDummy746 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy717 v u h)
          (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy708 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy717 v u h)
          (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy708 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_747`. -/
@[expose]
noncomputable def nb090AlphaDummy747 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy716 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_748`. -/
@[expose]
noncomputable def nb090AlphaDummy748 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy718 v u h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_749`. -/
@[expose]
noncomputable def nb090AlphaDummy749 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy716 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy716 A)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
