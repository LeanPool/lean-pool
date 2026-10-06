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

/-! Certificates from `NAR4C082C001Part001`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_000`. -/
@[expose]
noncomputable def nb082AlphaDummy000 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_001`. -/
@[expose]
noncomputable def nb082AlphaDummy001 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪ ((synCxpk B B)).fv ∪
      ((synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_002`. -/
@[expose]
noncomputable def nb082AlphaDummy002 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (({ p } : Finset Var) ∪ ((synCxpk B B)).fv ∪
      ((synCfdminvalp R A B (Class.cv p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_003`. -/
@[expose]
noncomputable def nb082AlphaDummy003 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪
        ({(nb082AlphaDummy001 A B R)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
          (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
            (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_004`. -/
@[expose]
noncomputable def nb082AlphaDummy004 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (({ p } : Finset Var) ∪ ({(nb082AlphaDummy002 A B R p)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv p) (synCxpk B B))
          (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
            (synCfdminvalp R A B (Class.cv p))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_005`. -/
@[expose]
noncomputable def nb082AlphaDummy005 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
      ((Class.cv (nb082AlphaDummy001 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_006`. -/
@[expose]
noncomputable def nb082AlphaDummy006 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
      ((Class.cv (nb082AlphaDummy001 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_007`. -/
@[expose]
noncomputable def nb082AlphaDummy007 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_008`. -/
@[expose]
noncomputable def nb082AlphaDummy008 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_009`. -/
@[expose]
noncomputable def nb082AlphaDummy009 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb082AlphaDummy005 A B R)
            (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCphi (Class.cv (nb082AlphaDummy006 A B R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_010`. -/
@[expose]
noncomputable def nb082AlphaDummy010 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCcompl (Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))))))).fv ∪ ((synCcompl
          (Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
              (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_011`. -/
@[expose]
noncomputable def nb082AlphaDummy011 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb082AlphaDummy005 A B R)
          (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy000 A B R))
            (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
              (synCphi (Class.cv (nb082AlphaDummy006 A B R))))))).fv ∪
      ((Class.cab (nb082AlphaDummy005 A B R)
          (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy000 A B R))
            (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
              (synCphi (Class.cv (nb082AlphaDummy006 A B R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_012`. -/
@[expose]
noncomputable def nb082AlphaDummy012 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cab (nb082AlphaDummy007 A B R p)
          (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
            (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
              (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))))).fv ∪
      ((Class.cab (nb082AlphaDummy007 A B R p)
          (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
            (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
              (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_013`. -/
@[expose]
noncomputable def nb082AlphaDummy013 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy006 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_014`. -/
@[expose]
noncomputable def nb082AlphaDummy014 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy006 A B R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_015`. -/
@[expose]
noncomputable def nb082AlphaDummy015 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy008 A B R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_016`. -/
@[expose]
noncomputable def nb082AlphaDummy016 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy008 A B R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_017`. -/
@[expose]
noncomputable def nb082AlphaDummy017 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb082AlphaDummy013 A B R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb082AlphaDummy013 A B R)) (synC1c))).fv ∪
      ((Class.cv (nb082AlphaDummy013 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_018`. -/
@[expose]
noncomputable def nb082AlphaDummy018 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb082AlphaDummy015 A B R p)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb082AlphaDummy015 A B R p)) (synC1c))).fv ∪
      ((Class.cv (nb082AlphaDummy015 A B R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_019`. -/
@[expose]
noncomputable def nb082AlphaDummy019 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_020`. -/
@[expose]
noncomputable def nb082AlphaDummy020 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_021`. -/
@[expose]
noncomputable def nb082AlphaDummy021 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_022`. -/
@[expose]
noncomputable def nb082AlphaDummy022 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_023`. -/
@[expose]
noncomputable def nb082AlphaDummy023 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_024`. -/
@[expose]
noncomputable def nb082AlphaDummy024 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_025`. -/
@[expose]
noncomputable def nb082AlphaDummy025 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb082AlphaDummy020 A B R))
          (Class.cv (nb082AlphaDummy021 A B R)))).fv ∪
      ((synCnin (Class.cv (nb082AlphaDummy020 A B R))
          (Class.cv (nb082AlphaDummy021 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_026`. -/
@[expose]
noncomputable def nb082AlphaDummy026 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
          (Class.cv (nb082AlphaDummy024 A B R p)))).fv ∪
      ((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
          (Class.cv (nb082AlphaDummy024 A B R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_027`. -/
@[expose]
noncomputable def nb082AlphaDummy027 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
      ((Class.cv (nb082AlphaDummy021 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_028`. -/
@[expose]
noncomputable def nb082AlphaDummy028 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
      ((Class.cv (nb082AlphaDummy024 A B R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_029`. -/
@[expose]
noncomputable def nb082AlphaDummy029 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb082AlphaDummy020 A B R)))).fv ∪
      ((synCcompl (Class.cv (nb082AlphaDummy021 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_030`. -/
@[expose]
noncomputable def nb082AlphaDummy030 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCcompl (Class.cv (nb082AlphaDummy023 A B R p)))).fv ∪
      ((synCcompl (Class.cv (nb082AlphaDummy024 A B R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_031`. -/
@[expose]
noncomputable def nb082AlphaDummy031 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
      ((Class.cv (nb082AlphaDummy020 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_032`. -/
@[expose]
noncomputable def nb082AlphaDummy032 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
      ((Class.cv (nb082AlphaDummy023 A B R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_033`. -/
@[expose]
noncomputable def nb082AlphaDummy033 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy021 A B R))).fv ∪
      ((Class.cv (nb082AlphaDummy021 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_034`. -/
@[expose]
noncomputable def nb082AlphaDummy034 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy024 A B R p))).fv ∪
      ((Class.cv (nb082AlphaDummy024 A B R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_035`. -/
@[expose]
noncomputable def nb082AlphaDummy035 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb082AlphaDummy005 A B R)
          (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy001 A B R))
            (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
              (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb082AlphaDummy005 A B R)
          (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy001 A B R))
            (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
              (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_036`. -/
@[expose]
noncomputable def nb082AlphaDummy036 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cab (nb082AlphaDummy007 A B R p)
          (synWrex (nb082AlphaDummy008 A B R p) (Class.cv (nb082AlphaDummy002 A B R p))
            (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
              (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb082AlphaDummy007 A B R p)
          (synWrex (nb082AlphaDummy008 A B R p) (Class.cv (nb082AlphaDummy002 A B R p))
            (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
              (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_037`. -/
@[expose]
noncomputable def nb082AlphaDummy037 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb082AlphaDummy006 A B R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_038`. -/
@[expose]
noncomputable def nb082AlphaDummy038 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_039`. -/
@[expose]
noncomputable def nb082AlphaDummy039 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb082AlphaDummy006 A B R)))).fv ∪
      ((synCphi (Class.cv (nb082AlphaDummy006 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_040`. -/
@[expose]
noncomputable def nb082AlphaDummy040 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCphi (Class.cv (nb082AlphaDummy008 A B R p)))).fv ∪
      ((synCphi (Class.cv (nb082AlphaDummy008 A B R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_041`. -/
@[expose]
noncomputable def nb082AlphaDummy041 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
          (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_042`. -/
@[expose]
noncomputable def nb082AlphaDummy042 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
          (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_043`. -/
@[expose]
noncomputable def nb082AlphaDummy043 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
        (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_044`. -/
@[expose]
noncomputable def nb082AlphaDummy044 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
        (synC1c))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_045`. -/
@[expose]
noncomputable def nb082AlphaDummy045 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCnin (synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv ∪ ((synCnin
          (synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_046`. -/
@[expose]
noncomputable def nb082AlphaDummy046 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
          (synC1c))).fv ∪
      ((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
          (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_047`. -/
@[expose]
noncomputable def nb082AlphaDummy047 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCimak (synCcnvk (synCfdminsep R A B))
          (synCsn (Class.cv (nb082AlphaDummy000 A B R))))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_048`. -/
@[expose]
noncomputable def nb082AlphaDummy048 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))).fv ∪
      ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_049`. -/
@[expose]
noncomputable def nb082AlphaDummy049 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪
      ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_050`. -/
@[expose]
noncomputable def nb082AlphaDummy050 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪
      ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_051`. -/
@[expose]
noncomputable def nb082AlphaDummy051 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_052`. -/
@[expose]
noncomputable def nb082AlphaDummy052 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_053`. -/
@[expose]
noncomputable def nb082AlphaDummy053 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy000 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_054`. -/
@[expose]
noncomputable def nb082AlphaDummy054 (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_055`. -/
@[expose]
noncomputable def nb082AlphaDummy055 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R)))))).fv ∪
      ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_056`. -/
@[expose]
noncomputable def nb082AlphaDummy056 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p)))))).fv ∪
      ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_057`. -/
@[expose]
noncomputable def nb082AlphaDummy057 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
      ((synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_058`. -/
@[expose]
noncomputable def nb082AlphaDummy058 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
      ((synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_059`. -/
@[expose]
noncomputable def nb082AlphaDummy059 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_060`. -/
@[expose]
noncomputable def nb082AlphaDummy060 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_061`. -/
@[expose]
noncomputable def nb082AlphaDummy061 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy050 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_062`. -/
@[expose]
noncomputable def nb082AlphaDummy062 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy052 A B R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_063`. -/
@[expose]
noncomputable def nb082AlphaDummy063 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
            (Class.cv (nb082AlphaDummy049 A B R))))).fv ∪ ((synCsn
          (synCpr (Class.cv (nb082AlphaDummy050 A B R))
            (Class.cv (nb082AlphaDummy049 A B R))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_064`. -/
@[expose]
noncomputable def nb082AlphaDummy064 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
            (Class.cv (nb082AlphaDummy051 A B R p))))).fv ∪ ((synCsn
          (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
            (Class.cv (nb082AlphaDummy051 A B R p))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_065`. -/
@[expose]
noncomputable def nb082AlphaDummy065 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCpr (Class.cv (nb082AlphaDummy050 A B R))
        (Class.cv (nb082AlphaDummy049 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_066`. -/
@[expose]
noncomputable def nb082AlphaDummy066 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCpr (Class.cv (nb082AlphaDummy052 A B R p))
        (Class.cv (nb082AlphaDummy051 A B R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_067`. -/
@[expose]
noncomputable def nb082AlphaDummy067 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
      ((synCcompl (synCsn (Class.cv (nb082AlphaDummy049 A B R))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_068`. -/
@[expose]
noncomputable def nb082AlphaDummy068 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCcompl (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
      ((synCcompl (synCsn (Class.cv (nb082AlphaDummy051 A B R p))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_069`. -/
@[expose]
noncomputable def nb082AlphaDummy069 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv ∪
      ((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_070`. -/
@[expose]
noncomputable def nb082AlphaDummy070 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv ∪
      ((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_071`. -/
@[expose]
noncomputable def nb082AlphaDummy071 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((synCsn (Class.cv (nb082AlphaDummy049 A B R)))).fv ∪
      ((synCsn (Class.cv (nb082AlphaDummy049 A B R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_072`. -/
@[expose]
noncomputable def nb082AlphaDummy072 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((synCsn (Class.cv (nb082AlphaDummy051 A B R p)))).fv ∪
      ((synCsn (Class.cv (nb082AlphaDummy051 A B R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_073`. -/
@[expose]
noncomputable def nb082AlphaDummy073 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb082AlphaDummy049 A B R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb082_alpha_dummy_074`. -/
@[expose]
noncomputable def nb082AlphaDummy074 (A : Class) (B : Class) (R : Class) (p : Var) :
    Var :=
  (freshVar (((Class.cv (nb082AlphaDummy051 A B R p))).fv) 0)

theorem nb082_fresh_000 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy011 A B R) ∉
      (((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCphi (Class.cv (nb082AlphaDummy006 A B R))))))).fv ∪
        ((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCphi (Class.cv (nb082AlphaDummy006 A B R))))))).fv) :=
  by
  simpa only [nb082AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCphi (Class.cv (nb082AlphaDummy006 A B R))))))).fv ∪
        ((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCphi (Class.cv (nb082AlphaDummy006 A B R))))))).fv)
      0

theorem nb082_fresh_001 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy035 A B R) ∉
      (((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb082AlphaDummy005 A B R)
            (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb082AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb082AlphaDummy005 A B R)
            (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb082_fresh_002 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy036 A B R p) ∉
      (((Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
              (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb082AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
              (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb082_fresh_003 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy012 A B R p) ∉
      (((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))))).fv ∪
        ((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))))).fv) :=
  by
  simpa only [nb082AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))))).fv ∪
        ((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))))).fv)
      0

theorem nb082_fresh_004 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy053 A B R) ∉ (((Class.cv (nb082AlphaDummy000 A B R))).fv) := by
  simpa only [nb082AlphaDummy053] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy000 A B R))).fv) 0

theorem nb082_fresh_005 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy005 A B R) ∉
      (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy001 A B R))).fv) :=
  by
  simpa only [nb082AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy001 A B R))).fv)
      0

theorem nb082_fresh_006 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy006 A B R) ∉
      (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy001 A B R))).fv) :=
  by
  simpa only [nb082AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy001 A B R))).fv)
      1

theorem nb082_distinct_007 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy005 A B R) ≠ (nb082AlphaDummy006 A B R) := by
  simpa only [nb082AlphaDummy005, nb082AlphaDummy006] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy001 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_008 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy013 A B R) ∉ (((Class.cv (nb082AlphaDummy006 A B R))).fv) := by
  simpa only [nb082AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy006 A B R))).fv) 0

theorem nb082_fresh_009 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy014 A B R) ∉ (((Class.cv (nb082AlphaDummy006 A B R))).fv) := by
  simpa only [nb082AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy006 A B R))).fv) 1

theorem nb082_distinct_010 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy013 A B R) ≠ (nb082AlphaDummy014 A B R) := by
  simpa only [nb082AlphaDummy013, nb082AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy006 A B R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb082_fresh_011 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy015 A B R p) ∉ (((Class.cv (nb082AlphaDummy008 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy008 A B R p))).fv) 0

theorem nb082_fresh_012 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy016 A B R p) ∉ (((Class.cv (nb082AlphaDummy008 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy008 A B R p))).fv) 1

theorem nb082_distinct_013 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy016 A B R p) := by
  simpa only [nb082AlphaDummy015, nb082AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy008 A B R p))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb082_fresh_014 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy019 A B R) ∉
      (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb082AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) 0

theorem nb082_fresh_015 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy020 A B R) ∉
      (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb082AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) 1

theorem nb082_fresh_016 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy021 A B R) ∉
      (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb082AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) 2

theorem nb082_distinct_017 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy019 A B R) ≠ (nb082AlphaDummy020 A B R) := by
  simpa only [nb082AlphaDummy019, nb082AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb082_distinct_018 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy019 A B R) ≠ (nb082AlphaDummy021 A B R) := by
  simpa only [nb082AlphaDummy019, nb082AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb082_distinct_019 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy020 A B R) ≠ (nb082AlphaDummy021 A B R) := by
  simpa only [nb082AlphaDummy020, nb082AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb082_fresh_020 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy022 A B R p) ∉
      (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb082AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) 0

theorem nb082_fresh_021 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy023 A B R p) ∉
      (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb082AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) 1

theorem nb082_fresh_022 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy024 A B R p) ∉
      (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb082AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) 2

theorem nb082_distinct_023 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy022 A B R p) ≠ (nb082AlphaDummy023 A B R p) := by
  simpa only [nb082AlphaDummy022, nb082AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb082_distinct_024 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy022 A B R p) ≠ (nb082AlphaDummy024 A B R p) := by
  simpa only [nb082AlphaDummy022, nb082AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb082_distinct_025 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy024 A B R p) := by
  simpa only [nb082AlphaDummy023, nb082AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb082_fresh_026 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy031 A B R) ∉
      (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy020 A B R))).fv) :=
  by
  simpa only [nb082AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy020 A B R))).fv)
      0

theorem nb082_fresh_027 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy027 A B R) ∉
      (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy021 A B R))).fv) :=
  by
  simpa only [nb082AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy021 A B R))).fv)
      0

theorem nb082_fresh_028 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy033 A B R) ∉
      (((Class.cv (nb082AlphaDummy021 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy021 A B R))).fv) :=
  by
  simpa only [nb082AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb082AlphaDummy021 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy021 A B R))).fv)
      0

theorem nb082_fresh_029 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy032 A B R p) ∉
      (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy023 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy023 A B R p))).fv)
      0

theorem nb082_fresh_030 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy028 A B R p) ∉
      (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy024 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy024 A B R p))).fv)
      0

theorem nb082_fresh_031 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy034 A B R p) ∉
      (((Class.cv (nb082AlphaDummy024 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy024 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb082AlphaDummy024 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy024 A B R p))).fv)
      0

theorem nb082_fresh_032 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy073 A B R) ∉ (((Class.cv (nb082AlphaDummy049 A B R))).fv) := by
  simpa only [nb082AlphaDummy073] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy049 A B R))).fv) 0

theorem nb082_fresh_033 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy061 A B R) ∉ (((Class.cv (nb082AlphaDummy050 A B R))).fv) := by
  simpa only [nb082AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy050 A B R))).fv) 0

theorem nb082_fresh_034 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy074 A B R p) ∉ (((Class.cv (nb082AlphaDummy051 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy074] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy051 A B R p))).fv) 0

theorem nb082_fresh_035 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy062 A B R p) ∉ (((Class.cv (nb082AlphaDummy052 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb082AlphaDummy052 A B R p))).fv) 0

theorem nb082_fresh_036 (p : Var) : (nb082AlphaDummy054 p) ∉ (((Class.cv p)).fv) := by
  simpa only [nb082AlphaDummy054] using freshVar_not_mem (((Class.cv p)).fv) 0

theorem nb082_fresh_037 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy007 A B R p) ∉
      (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy007] using
    freshVar_not_mem (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv)
      0

theorem nb082_fresh_038 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy008 A B R p) ∉
      (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy008] using
    freshVar_not_mem (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv)
      1

theorem nb082_distinct_039 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy007 A B R p) ≠ (nb082AlphaDummy008 A B R p) := by
  simpa only [nb082AlphaDummy007, nb082AlphaDummy008] using
    (freshVar_injective
      (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb082_fresh_040 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy017 A B R) ∉
      (((Wff.classMem (Class.cv (nb082AlphaDummy013 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb082AlphaDummy013 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb082AlphaDummy013 A B R))).fv) :=
  by
  simpa only [nb082AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb082AlphaDummy013 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb082AlphaDummy013 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb082AlphaDummy013 A B R))).fv)
      0

theorem nb082_fresh_041 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy018 A B R p) ∉
      (((Wff.classMem (Class.cv (nb082AlphaDummy015 A B R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb082AlphaDummy015 A B R p)) (synC1c))).fv ∪
        ((Class.cv (nb082AlphaDummy015 A B R p))).fv) :=
  by
  simpa only [nb082AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb082AlphaDummy015 A B R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb082AlphaDummy015 A B R p)) (synC1c))).fv ∪
        ((Class.cv (nb082AlphaDummy015 A B R p))).fv)
      0

theorem nb082_fresh_042 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∉
      (((synCcnvk (synCfdminsep R A B))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy049] using
    freshVar_not_mem
      (((synCcnvk (synCfdminsep R A B))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv)
      0

theorem nb082_fresh_043 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∉
      (((synCcnvk (synCfdminsep R A B))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy050] using
    freshVar_not_mem
      (((synCcnvk (synCfdminsep R A B))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv)
      1

theorem nb082_distinct_044 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ≠ (nb082AlphaDummy050 A B R) := by
  simpa only [nb082AlphaDummy049, nb082AlphaDummy050] using
    (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_045 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∉
      (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) :=
  by
  simpa only [nb082AlphaDummy051] using
    freshVar_not_mem
      (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 0

theorem nb082_fresh_046 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∉
      (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) :=
  by
  simpa only [nb082AlphaDummy052] using
    freshVar_not_mem
      (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 1

theorem nb082_distinct_047 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy052 A B R p) := by
  simpa only [nb082AlphaDummy051, nb082AlphaDummy052] using
    (freshVar_injective
      (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb082_fresh_048 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy009 A B R) ∉
      (((synCcompl (Class.cab (nb082AlphaDummy005 A B R)
              (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCphi (Class.cv (nb082AlphaDummy006 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
                (Class.cv (nb082AlphaDummy001 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb082AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb082AlphaDummy005 A B R)
              (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCphi (Class.cv (nb082AlphaDummy006 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
                (Class.cv (nb082AlphaDummy001 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb082_fresh_049 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy010 A B R p) ∉
      (((synCcompl (Class.cab (nb082AlphaDummy007 A B R p)
              (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
                (Class.cv (nb082AlphaDummy002 A B R p))
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb082AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb082AlphaDummy007 A B R p)
              (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
                (Class.cv (nb082AlphaDummy002 A B R p))
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb082_fresh_050 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy029 A B R) ∉
      (((synCcompl (Class.cv (nb082AlphaDummy020 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb082AlphaDummy021 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb082AlphaDummy020 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb082AlphaDummy021 A B R)))).fv)
      0

theorem nb082_fresh_051 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy030 A B R p) ∉
      (((synCcompl (Class.cv (nb082AlphaDummy023 A B R p)))).fv ∪
        ((synCcompl (Class.cv (nb082AlphaDummy024 A B R p)))).fv) :=
  by
  simpa only [nb082AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb082AlphaDummy023 A B R p)))).fv ∪
        ((synCcompl (Class.cv (nb082AlphaDummy024 A B R p)))).fv)
      0

theorem nb082_fresh_052 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy037 A B R) ∉
      (((synCcompl (synCphi (Class.cv (nb082AlphaDummy006 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb082AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb082AlphaDummy006 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb082_fresh_053 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy038 A B R p) ∉
      (((synCcompl (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb082AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb082_fresh_054 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy067 A B R) ∉
      (((synCcompl (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb082AlphaDummy049 A B R))))).fv) :=
  by
  simpa only [nb082AlphaDummy067] using
    freshVar_not_mem
      (((synCcompl (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb082AlphaDummy049 A B R))))).fv)
      0

theorem nb082_fresh_055 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy068 A B R p) ∉
      (((synCcompl (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb082AlphaDummy051 A B R p))))).fv) :=
  by
  simpa only [nb082AlphaDummy068] using
    freshVar_not_mem
      (((synCcompl (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb082AlphaDummy051 A B R p))))).fv)
      0

theorem nb082_fresh_056 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy055 A B R) ∉
      (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R)))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
                (Class.cv (nb082AlphaDummy049 A B R)))))).fv) :=
  by
  simpa only [nb082AlphaDummy055] using
    freshVar_not_mem
      (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R)))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
                (Class.cv (nb082AlphaDummy049 A B R)))))).fv)
      0

theorem nb082_fresh_057 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy056 A B R p) ∉
      (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p)))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
                (Class.cv (nb082AlphaDummy051 A B R p)))))).fv) :=
  by
  simpa only [nb082AlphaDummy056] using
    freshVar_not_mem
      (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p)))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
                (Class.cv (nb082AlphaDummy051 A B R p)))))).fv)
      0

theorem nb082_fresh_058 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy047 A B R) ∉
      (((synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R))))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb082AlphaDummy047] using
    freshVar_not_mem
      (((synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R))))).fv ∪ ((synC1c)).fv)
      0

theorem nb082_fresh_059 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy048 A B R p) ∉
      (((synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))).fv ∪
        ((synC1c)).fv) :=
  by
  simpa only [nb082AlphaDummy048] using
    freshVar_not_mem
      (((synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))).fv ∪
        ((synC1c)).fv)
      0

theorem nb082_fresh_060 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy041 A B R) ∉
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv) :=
  by
  simpa only [nb082AlphaDummy041] using
    freshVar_not_mem
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
      0

theorem nb082_fresh_061 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy042 A B R) ∉
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv) :=
  by
  simpa only [nb082AlphaDummy042] using
    freshVar_not_mem
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
      1

theorem nb082_distinct_062 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy041 A B R) ≠ (nb082AlphaDummy042 A B R) := by
  simpa only [nb082AlphaDummy041, nb082AlphaDummy042] using
    (freshVar_injective (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb082_fresh_063 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy043 A B R p) ∉
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
          (synC1c))).fv) :=
  by
  simpa only [nb082AlphaDummy043] using
    freshVar_not_mem
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
          (synC1c))).fv)
      0

theorem nb082_fresh_064 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy044 A B R p) ∉
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
          (synC1c))).fv) :=
  by
  simpa only [nb082AlphaDummy044] using
    freshVar_not_mem
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
          (synC1c))).fv)
      1

theorem nb082_distinct_065 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy043 A B R p) ≠ (nb082AlphaDummy044 A B R p) := by
  simpa only [nb082AlphaDummy043, nb082AlphaDummy044] using
    (freshVar_injective
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
          (synC1c))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_066 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy025 A B R) ∉
      (((synCnin (Class.cv (nb082AlphaDummy020 A B R))
            (Class.cv (nb082AlphaDummy021 A B R)))).fv ∪
        ((synCnin (Class.cv (nb082AlphaDummy020 A B R))
            (Class.cv (nb082AlphaDummy021 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb082AlphaDummy020 A B R))
            (Class.cv (nb082AlphaDummy021 A B R)))).fv ∪
        ((synCnin (Class.cv (nb082AlphaDummy020 A B R))
            (Class.cv (nb082AlphaDummy021 A B R)))).fv)
      0

theorem nb082_fresh_067 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy026 A B R p) ∉
      (((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
            (Class.cv (nb082AlphaDummy024 A B R p)))).fv ∪
        ((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
            (Class.cv (nb082AlphaDummy024 A B R p)))).fv) :=
  by
  simpa only [nb082AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
            (Class.cv (nb082AlphaDummy024 A B R p)))).fv ∪
        ((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
            (Class.cv (nb082AlphaDummy024 A B R p)))).fv)
      0

theorem nb082_fresh_068 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy045 A B R) ∉
      (((synCnin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv ∪ ((synCnin
            (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv) :=
  by
  simpa only [nb082AlphaDummy045] using
    freshVar_not_mem
      (((synCnin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv ∪ ((synCnin
            (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
      0

theorem nb082_fresh_069 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy046 A B R p) ∉
      (((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv ∪
        ((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv) :=
  by
  simpa only [nb082AlphaDummy046] using
    freshVar_not_mem
      (((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv ∪
        ((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv)
      0

theorem nb082_fresh_070 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy039 A B R) ∉
      (((synCphi (Class.cv (nb082AlphaDummy006 A B R)))).fv ∪
        ((synCphi (Class.cv (nb082AlphaDummy006 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb082AlphaDummy006 A B R)))).fv ∪
        ((synCphi (Class.cv (nb082AlphaDummy006 A B R)))).fv)
      0

theorem nb082_fresh_071 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy040 A B R p) ∉
      (((synCphi (Class.cv (nb082AlphaDummy008 A B R p)))).fv ∪
        ((synCphi (Class.cv (nb082AlphaDummy008 A B R p)))).fv) :=
  by
  simpa only [nb082AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb082AlphaDummy008 A B R p)))).fv ∪
        ((synCphi (Class.cv (nb082AlphaDummy008 A B R p)))).fv)
      0

theorem nb082_fresh_072 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy065 A B R) ∉
      (((synCpr (Class.cv (nb082AlphaDummy050 A B R))
          (Class.cv (nb082AlphaDummy049 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy065] using
    freshVar_not_mem
      (((synCpr (Class.cv (nb082AlphaDummy050 A B R))
          (Class.cv (nb082AlphaDummy049 A B R)))).fv)
      0

theorem nb082_fresh_073 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy066 A B R p) ∉
      (((synCpr (Class.cv (nb082AlphaDummy052 A B R p))
          (Class.cv (nb082AlphaDummy051 A B R p)))).fv) :=
  by
  simpa only [nb082AlphaDummy066] using
    freshVar_not_mem
      (((synCpr (Class.cv (nb082AlphaDummy052 A B R p))
          (Class.cv (nb082AlphaDummy051 A B R p)))).fv)
      0

theorem nb082_fresh_074 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy071 A B R) ∉
      (((synCsn (Class.cv (nb082AlphaDummy049 A B R)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy049 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy071] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb082AlphaDummy049 A B R)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy049 A B R)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C082C001Part002`. -/


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

theorem nb082_fresh_075 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy059 A B R) ∉
      (((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy059] using
    freshVar_not_mem (((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv) 0

theorem nb082_fresh_076 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy069 A B R) ∉
      (((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy069] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv)
      0

theorem nb082_fresh_077 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy072 A B R p) ∉
      (((synCsn (Class.cv (nb082AlphaDummy051 A B R p)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy051 A B R p)))).fv) :=
  by
  simpa only [nb082AlphaDummy072] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb082AlphaDummy051 A B R p)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy051 A B R p)))).fv)
      0

theorem nb082_fresh_078 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy060 A B R p) ∉
      (((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv) :=
  by
  simpa only [nb082AlphaDummy060] using
    freshVar_not_mem (((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv) 0

theorem nb082_fresh_079 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy070 A B R p) ∉
      (((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv) :=
  by
  simpa only [nb082AlphaDummy070] using
    freshVar_not_mem
      (((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv)
      0

theorem nb082_fresh_080 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy063 A B R) ∉
      (((synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R))))).fv) :=
  by
  simpa only [nb082AlphaDummy063] using
    freshVar_not_mem
      (((synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R))))).fv)
      0

theorem nb082_fresh_081 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy064 A B R p) ∉
      (((synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p))))).fv) :=
  by
  simpa only [nb082AlphaDummy064] using
    freshVar_not_mem
      (((synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p))))).fv)
      0

theorem nb082_fresh_082 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy057 A B R) ∉
      (((synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv) :=
  by
  simpa only [nb082AlphaDummy057] using
    freshVar_not_mem
      (((synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv)
      0

theorem nb082_fresh_083 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy058 A B R p) ∉
      (((synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv) :=
  by
  simpa only [nb082AlphaDummy058] using
    freshVar_not_mem
      (((synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv)
      0

theorem nb082_fresh_084 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb082AlphaDummy000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb082_fresh_085 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∉
      (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪ ((synCxpk B B)).fv ∪
        ((synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))).fv) :=
  by
  simpa only [nb082AlphaDummy001] using
    freshVar_not_mem
      (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪ ((synCxpk B B)).fv ∪
        ((synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))).fv)
      0

theorem nb082_fresh_086 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy003 A B R) ∉
      (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪
          ({(nb082AlphaDummy001 A B R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
            (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
              (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))))).fv) :=
  by
  simpa only [nb082AlphaDummy003] using
    freshVar_not_mem
      (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪
          ({(nb082AlphaDummy001 A B R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
            (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
              (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))))).fv)
      0

theorem nb082_fresh_087 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy002 A B R p) ∉
      (({ p } : Finset Var) ∪ ((synCxpk B B)).fv ∪ ((synCfdminvalp R A B (Class.cv p))).fv) :=
  by
  simpa only [nb082AlphaDummy002] using
    freshVar_not_mem
      (({ p } : Finset Var) ∪ ((synCxpk B B)).fv ∪ ((synCfdminvalp R A B (Class.cv p))).fv)
      0

theorem nb082_fresh_088 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy004 A B R p) ∉
      (({ p } : Finset Var) ∪ ({(nb082AlphaDummy002 A B R p)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv p) (synCxpk B B))
            (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
              (synCfdminvalp R A B (Class.cv p))))).fv) :=
  by
  simpa only [nb082AlphaDummy004] using
    freshVar_not_mem
      (({ p } : Finset Var) ∪ ({(nb082AlphaDummy002 A B R p)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv p) (synCxpk B B))
            (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
              (synCfdminvalp R A B (Class.cv p))))).fv)
      0

theorem nb082_support_mem_0000 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪
          ({(nb082AlphaDummy001 A B R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
            (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
              (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0001 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈
      (({ p } : Finset Var) ∪ ({(nb082AlphaDummy002 A B R p)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv p) (synCxpk B B))
            (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
              (synCfdminvalp R A B (Class.cv p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0002 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∈
      (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪
          ({(nb082AlphaDummy001 A B R)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
            (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
              (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0003 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy002 A B R p) ∈
      (({ p } : Finset Var) ∪ ({(nb082AlphaDummy002 A B R p)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv p) (synCxpk B B))
            (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
              (synCfdminvalp R A B (Class.cv p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0004 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪ ((synCxpk B B)).fv ∪
        ((synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0005 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈
      (({ p } : Finset Var) ∪ ((synCxpk B B)).fv ∪ ((synCfdminvalp R A B (Class.cv p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0006 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy001 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0007 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (((synCcompl (Class.cab (nb082AlphaDummy005 A B R)
              (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCphi (Class.cv (nb082AlphaDummy006 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
                (Class.cv (nb082AlphaDummy001 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy005 A B R) from (by
          unfold nb082AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0006 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy006 A B R) from (by
            unfold nb082AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0006 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0008 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈ (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0009 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈
      (((synCcompl (Class.cab (nb082AlphaDummy007 A B R p)
              (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
                (Class.cv (nb082AlphaDummy002 A B R p))
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb082AlphaDummy007 A B R p) from (by
          unfold nb082AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0008 A B R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb082AlphaDummy008 A B R p) from (by
            unfold nb082AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0008 A B R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0010 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCphi (Class.cv (nb082AlphaDummy006 A B R))))))).fv ∪
        ((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy000 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCphi (Class.cv (nb082AlphaDummy006 A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy005 A B R) from (by
          unfold nb082AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0006 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy006 A B R) from (by
            unfold nb082AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0006 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0011 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈
      (((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))))).fv ∪
        ((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb082AlphaDummy007 A B R p) from (by
          unfold nb082AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0008 A B R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb082AlphaDummy008 A B R p) from (by
            unfold nb082AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0008 A B R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0012 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy006 A B R) ∈ (((Class.cv (nb082AlphaDummy006 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0013 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy008 A B R p) ∈ (((Class.cv (nb082AlphaDummy008 A B R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0014 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy013 A B R) ∈
      (((Wff.classMem (Class.cv (nb082AlphaDummy013 A B R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb082AlphaDummy013 A B R)) (synC1c))).fv ∪
        ((Class.cv (nb082AlphaDummy013 A B R))).fv) :=
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

theorem nb082_support_mem_0015 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy015 A B R p) ∈
      (((Wff.classMem (Class.cv (nb082AlphaDummy015 A B R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb082AlphaDummy015 A B R p)) (synC1c))).fv ∪
        ((Class.cv (nb082AlphaDummy015 A B R p))).fv) :=
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

theorem nb082_support_mem_0016 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy013 A B R) ∈
      (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0017 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy015 A B R p) ∈
      (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0018 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy020 A B R) ∈
      (((synCnin (Class.cv (nb082AlphaDummy020 A B R))
            (Class.cv (nb082AlphaDummy021 A B R)))).fv ∪
        ((synCnin (Class.cv (nb082AlphaDummy020 A B R))
            (Class.cv (nb082AlphaDummy021 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0019 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy023 A B R p) ∈
      (((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
            (Class.cv (nb082AlphaDummy024 A B R p)))).fv ∪
        ((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
            (Class.cv (nb082AlphaDummy024 A B R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0020 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy020 A B R) ∈
      (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy021 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0021 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy023 A B R p) ∈
      (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy024 A B R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0022 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy021 A B R) ∈
      (((synCnin (Class.cv (nb082AlphaDummy020 A B R))
            (Class.cv (nb082AlphaDummy021 A B R)))).fv ∪
        ((synCnin (Class.cv (nb082AlphaDummy020 A B R))
            (Class.cv (nb082AlphaDummy021 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0023 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy024 A B R p) ∈
      (((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
            (Class.cv (nb082AlphaDummy024 A B R p)))).fv ∪
        ((synCnin (Class.cv (nb082AlphaDummy023 A B R p))
            (Class.cv (nb082AlphaDummy024 A B R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0024 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy021 A B R) ∈
      (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy021 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0025 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy024 A B R p) ∈
      (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy024 A B R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0026 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy020 A B R) ∈
      (((synCcompl (Class.cv (nb082AlphaDummy020 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb082AlphaDummy021 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0027 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy023 A B R p) ∈
      (((synCcompl (Class.cv (nb082AlphaDummy023 A B R p)))).fv ∪
        ((synCcompl (Class.cv (nb082AlphaDummy024 A B R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0028 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy020 A B R) ∈
      (((Class.cv (nb082AlphaDummy020 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy020 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0029 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy023 A B R p) ∈
      (((Class.cv (nb082AlphaDummy023 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy023 A B R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0030 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy021 A B R) ∈
      (((synCcompl (Class.cv (nb082AlphaDummy020 A B R)))).fv ∪
        ((synCcompl (Class.cv (nb082AlphaDummy021 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0031 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy024 A B R p) ∈
      (((synCcompl (Class.cv (nb082AlphaDummy023 A B R p)))).fv ∪
        ((synCcompl (Class.cv (nb082AlphaDummy024 A B R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0032 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy021 A B R) ∈
      (((Class.cv (nb082AlphaDummy021 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy021 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0033 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy024 A B R p) ∈
      (((Class.cv (nb082AlphaDummy024 A B R p))).fv ∪
        ((Class.cv (nb082AlphaDummy024 A B R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0034 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∈
      (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
        ((Class.cv (nb082AlphaDummy001 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0035 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∈
      (((synCcompl (Class.cab (nb082AlphaDummy005 A B R)
              (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCphi (Class.cv (nb082AlphaDummy006 A B R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
                (Class.cv (nb082AlphaDummy001 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy005 A B R) from (by
          unfold nb082AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0034 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy006 A B R) from (by
            unfold nb082AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0034 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0036 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy002 A B R p) ∈
      (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0037 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy002 A B R p) ∈
      (((synCcompl (Class.cab (nb082AlphaDummy007 A B R p)
              (synWrex (nb082AlphaDummy008 A B R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
                (Class.cv (nb082AlphaDummy002 A B R p))
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy007 A B R p) from (by
          unfold nb082AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy008 A B R p) from (by
            unfold nb082AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0038 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∈
      (((Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb082AlphaDummy005 A B R)
            (synWrex (nb082AlphaDummy006 A B R) (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy005 A B R) from (by
          unfold nb082AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0034 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy006 A B R) from (by
            unfold nb082AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0034 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0039 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy002 A B R p) ∈
      (((Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
              (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb082AlphaDummy007 A B R p)
            (synWrex (nb082AlphaDummy008 A B R p) (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy007 A B R p) from (by
          unfold nb082AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy008 A B R p) from (by
            unfold nb082AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0040 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy006 A B R) ∈
      (((synCcompl (synCphi (Class.cv (nb082AlphaDummy006 A B R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0041 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy008 A B R p) ∈
      (((synCcompl (synCphi (Class.cv (nb082AlphaDummy008 A B R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0042 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy006 A B R) ∈
      (((synCphi (Class.cv (nb082AlphaDummy006 A B R)))).fv ∪
        ((synCphi (Class.cv (nb082AlphaDummy006 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0043 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy008 A B R p) ∈
      (((synCphi (Class.cv (nb082AlphaDummy008 A B R p)))).fv ∪
        ((synCphi (Class.cv (nb082AlphaDummy008 A B R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0044 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv) :=
  by
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cimak]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0045 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈
      (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
          (synC1c))).fv) :=
  by
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cimak]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0046 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (((synCnin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv ∪ ((synCnin
            (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cimak]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0047 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈
      (((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv ∪
        ((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cimak]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0048 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (((synCimak (synCcnvk (synCfdminsep R A B))
            (synCsn (Class.cv (nb082AlphaDummy000 A B R))))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cimak]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0049 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈
      (((synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))).fv ∪
        ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cimak]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0050 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈
      (((synCcnvk (synCfdminsep R A B))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0051 (A : Class) (B : Class) (R : Class) (p : Var) :
    p ∈ (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0052 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∈ (((Class.cv (nb082AlphaDummy000 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0053 (p : Var) : p ∈ (((Class.cv p)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0054 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∈
      (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R)))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
                (Class.cv (nb082AlphaDummy049 A B R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0055 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∈
      (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p)))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
                (Class.cv (nb082AlphaDummy051 A B R p)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0056 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∈
      (((synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0057 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∈
      (((synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
        ((synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0058 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∈
      (((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0059 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∈
      (((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv) :=
  by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0060 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∈ (((Class.cv (nb082AlphaDummy050 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0061 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∈ (((Class.cv (nb082AlphaDummy052 A B R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0062 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∈
      (((synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0063 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∈
      (((synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0064 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∈
      (((synCpr (Class.cv (nb082AlphaDummy050 A B R))
          (Class.cv (nb082AlphaDummy049 A B R)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0065 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∈
      (((synCpr (Class.cv (nb082AlphaDummy052 A B R p))
          (Class.cv (nb082AlphaDummy051 A B R p)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0066 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∈
      (((synCcompl (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb082AlphaDummy049 A B R))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0067 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∈
      (((synCcompl (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb082AlphaDummy051 A B R p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0068 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∈
      (((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy050 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0069 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∈
      (((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy052 A B R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0070 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∈
      (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy050 A B R)))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
                (Class.cv (nb082AlphaDummy049 A B R)))))).fv) :=
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

theorem nb082_support_mem_0071 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∈
      (((synCcompl (synCsn (synCsn (Class.cv (nb082AlphaDummy052 A B R p)))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
                (Class.cv (nb082AlphaDummy051 A B R p)))))).fv) :=
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

theorem nb082_support_mem_0072 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∈
      (((synCsn (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb082AlphaDummy050 A B R))
              (Class.cv (nb082AlphaDummy049 A B R))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0073 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∈
      (((synCsn (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p))))).fv ∪ ((synCsn
            (synCpr (Class.cv (nb082AlphaDummy052 A B R p))
              (Class.cv (nb082AlphaDummy051 A B R p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0074 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∈
      (((synCpr (Class.cv (nb082AlphaDummy050 A B R))
          (Class.cv (nb082AlphaDummy049 A B R)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0075 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∈
      (((synCpr (Class.cv (nb082AlphaDummy052 A B R p))
          (Class.cv (nb082AlphaDummy051 A B R p)))).fv) :=
  by
  rw [fv_syn_cpr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0076 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∈
      (((synCcompl (synCsn (Class.cv (nb082AlphaDummy050 A B R))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb082AlphaDummy049 A B R))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0077 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∈
      (((synCcompl (synCsn (Class.cv (nb082AlphaDummy052 A B R p))))).fv ∪
        ((synCcompl (synCsn (Class.cv (nb082AlphaDummy051 A B R p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0078 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∈
      (((synCsn (Class.cv (nb082AlphaDummy049 A B R)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy049 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0079 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∈
      (((synCsn (Class.cv (nb082AlphaDummy051 A B R p)))).fv ∪
        ((synCsn (Class.cv (nb082AlphaDummy051 A B R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0080 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∈ (((Class.cv (nb082AlphaDummy049 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0081 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∈ (((Class.cv (nb082AlphaDummy051 A B R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
