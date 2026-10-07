/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4H5C096M3Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_000`. -/
@[expose]
noncomputable def nb096AlphaDummy000 (D : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_001`. -/
@[expose]
noncomputable def nb096AlphaDummy001 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb096AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪
      ((synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_002`. -/
@[expose]
noncomputable def nb096AlphaDummy002 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (({ q } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_003`. -/
@[expose]
noncomputable def nb096AlphaDummy003 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb096AlphaDummy000 D R)} : Finset Var) ∪
        ({(nb096AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
          (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_004`. -/
@[expose]
noncomputable def nb096AlphaDummy004 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (({ q } : Finset Var) ∪ ({(nb096AlphaDummy002 D R q)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
          (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv q)))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_005`. -/
@[expose]
noncomputable def nb096AlphaDummy005 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy001 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_006`. -/
@[expose]
noncomputable def nb096AlphaDummy006 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy001 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_007`. -/
@[expose]
noncomputable def nb096AlphaDummy007 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_008`. -/
@[expose]
noncomputable def nb096AlphaDummy008 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_009`. -/
@[expose]
noncomputable def nb096AlphaDummy009 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCphi (Class.cv (nb096AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_010`. -/
@[expose]
noncomputable def nb096AlphaDummy010 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCphi (Class.cv (nb096AlphaDummy008 D R q)))))))).fv ∪ ((synCcompl
          (Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
              (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_011`. -/
@[expose]
noncomputable def nb096AlphaDummy011 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy005 D R)
          (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
              (synCphi (Class.cv (nb096AlphaDummy006 D R))))))).fv ∪
      ((Class.cab (nb096AlphaDummy005 D R)
          (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
              (synCphi (Class.cv (nb096AlphaDummy006 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_012`. -/
@[expose]
noncomputable def nb096AlphaDummy012 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy007 D R q)
          (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
            (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
              (synCphi (Class.cv (nb096AlphaDummy008 D R q))))))).fv ∪
      ((Class.cab (nb096AlphaDummy007 D R q)
          (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
            (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
              (synCphi (Class.cv (nb096AlphaDummy008 D R q))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_013`. -/
@[expose]
noncomputable def nb096AlphaDummy013 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy006 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_014`. -/
@[expose]
noncomputable def nb096AlphaDummy014 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy006 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_015`. -/
@[expose]
noncomputable def nb096AlphaDummy015 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy008 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_016`. -/
@[expose]
noncomputable def nb096AlphaDummy016 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy008 D R q))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_017`. -/
@[expose]
noncomputable def nb096AlphaDummy017 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096AlphaDummy013 D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb096AlphaDummy013 D R)) (synC1c))).fv ∪
      ((Class.cv (nb096AlphaDummy013 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_018`. -/
@[expose]
noncomputable def nb096AlphaDummy018 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096AlphaDummy015 D R q)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb096AlphaDummy015 D R q)) (synC1c))).fv ∪
      ((Class.cv (nb096AlphaDummy015 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_019`. -/
@[expose]
noncomputable def nb096AlphaDummy019 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_020`. -/
@[expose]
noncomputable def nb096AlphaDummy020 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_021`. -/
@[expose]
noncomputable def nb096AlphaDummy021 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_022`. -/
@[expose]
noncomputable def nb096AlphaDummy022 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_023`. -/
@[expose]
noncomputable def nb096AlphaDummy023 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_024`. -/
@[expose]
noncomputable def nb096AlphaDummy024 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_025`. -/
@[expose]
noncomputable def nb096AlphaDummy025 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb096AlphaDummy020 D R))
          (Class.cv (nb096AlphaDummy021 D R)))).fv ∪
      ((synCnin (Class.cv (nb096AlphaDummy020 D R))
          (Class.cv (nb096AlphaDummy021 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_026`. -/
@[expose]
noncomputable def nb096AlphaDummy026 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb096AlphaDummy023 D R q))
          (Class.cv (nb096AlphaDummy024 D R q)))).fv ∪
      ((synCnin (Class.cv (nb096AlphaDummy023 D R q))
          (Class.cv (nb096AlphaDummy024 D R q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_027`. -/
@[expose]
noncomputable def nb096AlphaDummy027 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy021 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_028`. -/
@[expose]
noncomputable def nb096AlphaDummy028 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
      ((Class.cv (nb096AlphaDummy024 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_029`. -/
@[expose]
noncomputable def nb096AlphaDummy029 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb096AlphaDummy020 D R)))).fv ∪
      ((synCcompl (Class.cv (nb096AlphaDummy021 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_030`. -/
@[expose]
noncomputable def nb096AlphaDummy030 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb096AlphaDummy023 D R q)))).fv ∪
      ((synCcompl (Class.cv (nb096AlphaDummy024 D R q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_031`. -/
@[expose]
noncomputable def nb096AlphaDummy031 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy020 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_032`. -/
@[expose]
noncomputable def nb096AlphaDummy032 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
      ((Class.cv (nb096AlphaDummy023 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_033`. -/
@[expose]
noncomputable def nb096AlphaDummy033 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy021 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy021 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_034`. -/
@[expose]
noncomputable def nb096AlphaDummy034 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy024 D R q))).fv ∪
      ((Class.cv (nb096AlphaDummy024 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_035`. -/
@[expose]
noncomputable def nb096AlphaDummy035 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy005 D R)
          (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
              (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy005 D R)
          (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
              (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_036`. -/
@[expose]
noncomputable def nb096AlphaDummy036 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy007 D R q)
          (synWrex (nb096AlphaDummy008 D R q) (Class.cv (nb096AlphaDummy002 D R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
              (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy007 D R q)
          (synWrex (nb096AlphaDummy008 D R q) (Class.cv (nb096AlphaDummy002 D R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
              (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_037`. -/
@[expose]
noncomputable def nb096AlphaDummy037 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb096AlphaDummy006 D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_038`. -/
@[expose]
noncomputable def nb096AlphaDummy038 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb096AlphaDummy008 D R q))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_039`. -/
@[expose]
noncomputable def nb096AlphaDummy039 (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb096AlphaDummy006 D R)))).fv ∪
      ((synCphi (Class.cv (nb096AlphaDummy006 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_040`. -/
@[expose]
noncomputable def nb096AlphaDummy040 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb096AlphaDummy008 D R q)))).fv ∪
      ((synCphi (Class.cv (nb096AlphaDummy008 D R q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_041`. -/
@[expose]
noncomputable def nb096AlphaDummy041 (D : Class) (R : Class) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_042`. -/
@[expose]
noncomputable def nb096AlphaDummy042 (D : Class) (R : Class) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_043`. -/
@[expose]
noncomputable def nb096AlphaDummy043 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_044`. -/
@[expose]
noncomputable def nb096AlphaDummy044 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_045`. -/
@[expose]
noncomputable def nb096AlphaDummy045 (D : Class) (R : Class) : Var :=
  (freshVar (((synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_046`. -/
@[expose]
noncomputable def nb096AlphaDummy046 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv q))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_047`. -/
@[expose]
noncomputable def nb096AlphaDummy047 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv ∪
      ((synCnin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_048`. -/
@[expose]
noncomputable def nb096AlphaDummy048 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q))))))).fv ∪ ((synCnin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_049`. -/
@[expose]
noncomputable def nb096AlphaDummy049 (D : Class) (R : Class) : Var :=
  (freshVar ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_050`. -/
@[expose]
noncomputable def nb096AlphaDummy050 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv q)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_051`. -/
@[expose]
noncomputable def nb096AlphaDummy051 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_052`. -/
@[expose]
noncomputable def nb096AlphaDummy052 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_053`. -/
@[expose]
noncomputable def nb096AlphaDummy053 (R : Class) (q : Var) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (synCuni (synCuni (Class.cv q))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_054`. -/
@[expose]
noncomputable def nb096AlphaDummy054 (R : Class) (q : Var) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (synCuni (synCuni (Class.cv q))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_055`. -/
@[expose]
noncomputable def nb096AlphaDummy055 (D : Class) (R : Class) : Var :=
  (freshVar (((synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_056`. -/
@[expose]
noncomputable def nb096AlphaDummy056 (q : Var) : Var :=
  (freshVar (((synCuni (synCuni (Class.cv q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_057`. -/
@[expose]
noncomputable def nb096AlphaDummy057 (D : Class) (R : Class) : Var :=
  (freshVar (((synCuni (Class.cv (nb096AlphaDummy000 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_058`. -/
@[expose]
noncomputable def nb096AlphaDummy058 (D : Class) (R : Class) : Var :=
  (freshVar (((synCuni (Class.cv (nb096AlphaDummy000 D R)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_059`. -/
@[expose]
noncomputable def nb096AlphaDummy059 (q : Var) : Var :=
  (freshVar (((synCuni (Class.cv q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_060`. -/
@[expose]
noncomputable def nb096AlphaDummy060 (q : Var) : Var :=
  (freshVar (((synCuni (Class.cv q))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_061`. -/
@[expose]
noncomputable def nb096AlphaDummy061 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy000 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_062`. -/
@[expose]
noncomputable def nb096AlphaDummy062 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy000 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_063`. -/
@[expose]
noncomputable def nb096AlphaDummy063 (q : Var) : Var :=
  (freshVar (((Class.cv q)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_064`. -/
@[expose]
noncomputable def nb096AlphaDummy064 (q : Var) : Var :=
  (freshVar (((Class.cv q)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_065`. -/
@[expose]
noncomputable def nb096AlphaDummy065 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy051 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_066`. -/
@[expose]
noncomputable def nb096AlphaDummy066 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy051 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_067`. -/
@[expose]
noncomputable def nb096AlphaDummy067 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
      ((Class.cv (nb096AlphaDummy053 R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_068`. -/
@[expose]
noncomputable def nb096AlphaDummy068 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
      ((Class.cv (nb096AlphaDummy053 R q))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_069`. -/
@[expose]
noncomputable def nb096AlphaDummy069 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCphi (Class.cv (nb096AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_070`. -/
@[expose]
noncomputable def nb096AlphaDummy070 (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCphi (Class.cv (nb096AlphaDummy068 R q)))))))).fv ∪ ((synCcompl
          (Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_071`. -/
@[expose]
noncomputable def nb096AlphaDummy071 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy065 D R)
          (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
              (synCphi (Class.cv (nb096AlphaDummy066 D R))))))).fv ∪
      ((Class.cab (nb096AlphaDummy065 D R)
          (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
              (synCphi (Class.cv (nb096AlphaDummy066 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_072`. -/
@[expose]
noncomputable def nb096AlphaDummy072 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy067 R q)
          (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
              (synCphi (Class.cv (nb096AlphaDummy068 R q))))))).fv ∪
      ((Class.cab (nb096AlphaDummy067 R q)
          (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
              (synCphi (Class.cv (nb096AlphaDummy068 R q))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_073`. -/
@[expose]
noncomputable def nb096AlphaDummy073 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy066 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_074`. -/
@[expose]
noncomputable def nb096AlphaDummy074 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy066 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_075`. -/
@[expose]
noncomputable def nb096AlphaDummy075 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy068 R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_076`. -/
@[expose]
noncomputable def nb096AlphaDummy076 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy068 R q))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_077`. -/
@[expose]
noncomputable def nb096AlphaDummy077 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096AlphaDummy073 D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb096AlphaDummy073 D R)) (synC1c))).fv ∪
      ((Class.cv (nb096AlphaDummy073 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_078`. -/
@[expose]
noncomputable def nb096AlphaDummy078 (R : Class) (q : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096AlphaDummy075 R q)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb096AlphaDummy075 R q)) (synC1c))).fv ∪
      ((Class.cv (nb096AlphaDummy075 R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_079`. -/
@[expose]
noncomputable def nb096AlphaDummy079 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_080`. -/
@[expose]
noncomputable def nb096AlphaDummy080 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_081`. -/
@[expose]
noncomputable def nb096AlphaDummy081 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_082`. -/
@[expose]
noncomputable def nb096AlphaDummy082 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_083`. -/
@[expose]
noncomputable def nb096AlphaDummy083 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_084`. -/
@[expose]
noncomputable def nb096AlphaDummy084 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_085`. -/
@[expose]
noncomputable def nb096AlphaDummy085 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb096AlphaDummy080 D R))
          (Class.cv (nb096AlphaDummy081 D R)))).fv ∪
      ((synCnin (Class.cv (nb096AlphaDummy080 D R))
          (Class.cv (nb096AlphaDummy081 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_086`. -/
@[expose]
noncomputable def nb096AlphaDummy086 (R : Class) (q : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb096AlphaDummy083 R q))
          (Class.cv (nb096AlphaDummy084 R q)))).fv ∪
      ((synCnin (Class.cv (nb096AlphaDummy083 R q))
          (Class.cv (nb096AlphaDummy084 R q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_087`. -/
@[expose]
noncomputable def nb096AlphaDummy087 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy081 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_088`. -/
@[expose]
noncomputable def nb096AlphaDummy088 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
      ((Class.cv (nb096AlphaDummy084 R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_089`. -/
@[expose]
noncomputable def nb096AlphaDummy089 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb096AlphaDummy080 D R)))).fv ∪
      ((synCcompl (Class.cv (nb096AlphaDummy081 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_090`. -/
@[expose]
noncomputable def nb096AlphaDummy090 (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb096AlphaDummy083 R q)))).fv ∪
      ((synCcompl (Class.cv (nb096AlphaDummy084 R q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_091`. -/
@[expose]
noncomputable def nb096AlphaDummy091 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy080 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_092`. -/
@[expose]
noncomputable def nb096AlphaDummy092 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
      ((Class.cv (nb096AlphaDummy083 R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_093`. -/
@[expose]
noncomputable def nb096AlphaDummy093 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy081 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy081 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_094`. -/
@[expose]
noncomputable def nb096AlphaDummy094 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy084 R q))).fv ∪
      ((Class.cv (nb096AlphaDummy084 R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_095`. -/
@[expose]
noncomputable def nb096AlphaDummy095 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy065 D R)
          (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
              (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy065 D R)
          (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
              (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_096`. -/
@[expose]
noncomputable def nb096AlphaDummy096 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy067 R q)
          (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
              (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy067 R q)
          (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
              (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_097`. -/
@[expose]
noncomputable def nb096AlphaDummy097 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb096AlphaDummy066 D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_098`. -/
@[expose]
noncomputable def nb096AlphaDummy098 (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb096AlphaDummy068 R q))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_099`. -/
@[expose]
noncomputable def nb096AlphaDummy099 (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb096AlphaDummy066 D R)))).fv ∪
      ((synCphi (Class.cv (nb096AlphaDummy066 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_100`. -/
@[expose]
noncomputable def nb096AlphaDummy100 (R : Class) (q : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb096AlphaDummy068 R q)))).fv ∪
      ((synCphi (Class.cv (nb096AlphaDummy068 R q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_101`. -/
@[expose]
noncomputable def nb096AlphaDummy101 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy041 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_102`. -/
@[expose]
noncomputable def nb096AlphaDummy102 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy041 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_103`. -/
@[expose]
noncomputable def nb096AlphaDummy103 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
      ((Class.cv (nb096AlphaDummy043 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_104`. -/
@[expose]
noncomputable def nb096AlphaDummy104 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
      ((Class.cv (nb096AlphaDummy043 D R q))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_105`. -/
@[expose]
noncomputable def nb096AlphaDummy105 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCphi (Class.cv (nb096AlphaDummy102 D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_106`. -/
@[expose]
noncomputable def nb096AlphaDummy106 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb096AlphaDummy103 D R q)
            (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy044 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCphi (Class.cv (nb096AlphaDummy104 D R q)))))))).fv ∪ ((synCcompl
          (Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy043 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_107`. -/
@[expose]
noncomputable def nb096AlphaDummy107 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy101 D R)
          (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
              (synCphi (Class.cv (nb096AlphaDummy102 D R))))))).fv ∪
      ((Class.cab (nb096AlphaDummy101 D R)
          (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
              (synCphi (Class.cv (nb096AlphaDummy102 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_108`. -/
@[expose]
noncomputable def nb096AlphaDummy108 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy103 D R q)
          (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy044 D R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
              (synCphi (Class.cv (nb096AlphaDummy104 D R q))))))).fv ∪
      ((Class.cab (nb096AlphaDummy103 D R q)
          (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy044 D R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
              (synCphi (Class.cv (nb096AlphaDummy104 D R q))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_109`. -/
@[expose]
noncomputable def nb096AlphaDummy109 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy102 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_110`. -/
@[expose]
noncomputable def nb096AlphaDummy110 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy102 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_111`. -/
@[expose]
noncomputable def nb096AlphaDummy111 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy104 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_112`. -/
@[expose]
noncomputable def nb096AlphaDummy112 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy104 D R q))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_113`. -/
@[expose]
noncomputable def nb096AlphaDummy113 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096AlphaDummy109 D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb096AlphaDummy109 D R)) (synC1c))).fv ∪
      ((Class.cv (nb096AlphaDummy109 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_114`. -/
@[expose]
noncomputable def nb096AlphaDummy114 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096AlphaDummy111 D R q)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb096AlphaDummy111 D R q)) (synC1c))).fv ∪
      ((Class.cv (nb096AlphaDummy111 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_115`. -/
@[expose]
noncomputable def nb096AlphaDummy115 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_116`. -/
@[expose]
noncomputable def nb096AlphaDummy116 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_117`. -/
@[expose]
noncomputable def nb096AlphaDummy117 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_118`. -/
@[expose]
noncomputable def nb096AlphaDummy118 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_119`. -/
@[expose]
noncomputable def nb096AlphaDummy119 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_120`. -/
@[expose]
noncomputable def nb096AlphaDummy120 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_121`. -/
@[expose]
noncomputable def nb096AlphaDummy121 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb096AlphaDummy116 D R))
          (Class.cv (nb096AlphaDummy117 D R)))).fv ∪
      ((synCnin (Class.cv (nb096AlphaDummy116 D R))
          (Class.cv (nb096AlphaDummy117 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_122`. -/
@[expose]
noncomputable def nb096AlphaDummy122 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb096AlphaDummy119 D R q))
          (Class.cv (nb096AlphaDummy120 D R q)))).fv ∪
      ((synCnin (Class.cv (nb096AlphaDummy119 D R q))
          (Class.cv (nb096AlphaDummy120 D R q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_123`. -/
@[expose]
noncomputable def nb096AlphaDummy123 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy117 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_124`. -/
@[expose]
noncomputable def nb096AlphaDummy124 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
      ((Class.cv (nb096AlphaDummy120 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_125`. -/
@[expose]
noncomputable def nb096AlphaDummy125 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb096AlphaDummy116 D R)))).fv ∪
      ((synCcompl (Class.cv (nb096AlphaDummy117 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_126`. -/
@[expose]
noncomputable def nb096AlphaDummy126 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb096AlphaDummy119 D R q)))).fv ∪
      ((synCcompl (Class.cv (nb096AlphaDummy120 D R q)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_127`. -/
@[expose]
noncomputable def nb096AlphaDummy127 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy116 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_128`. -/
@[expose]
noncomputable def nb096AlphaDummy128 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
      ((Class.cv (nb096AlphaDummy119 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_129`. -/
@[expose]
noncomputable def nb096AlphaDummy129 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy117 D R))).fv ∪
      ((Class.cv (nb096AlphaDummy117 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_130`. -/
@[expose]
noncomputable def nb096AlphaDummy130 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096AlphaDummy120 D R q))).fv ∪
      ((Class.cv (nb096AlphaDummy120 D R q))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_131`. -/
@[expose]
noncomputable def nb096AlphaDummy131 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy101 D R)
          (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
              (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy101 D R)
          (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
            (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
              (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_132`. -/
@[expose]
noncomputable def nb096AlphaDummy132 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096AlphaDummy103 D R q)
          (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy043 D R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
              (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy103 D R q)
          (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy043 D R q))
            (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
              (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_133`. -/
@[expose]
noncomputable def nb096AlphaDummy133 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb096AlphaDummy102 D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_134`. -/
@[expose]
noncomputable def nb096AlphaDummy134 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb096AlphaDummy104 D R q))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_135`. -/
@[expose]
noncomputable def nb096AlphaDummy135 (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb096AlphaDummy102 D R)))).fv ∪
      ((synCphi (Class.cv (nb096AlphaDummy102 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_136`. -/
@[expose]
noncomputable def nb096AlphaDummy136 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb096AlphaDummy104 D R q)))).fv ∪
      ((synCphi (Class.cv (nb096AlphaDummy104 D R q)))).fv) 0)

theorem nb096_fresh_000 (D : Class) (R : Class) :
    (nb096AlphaDummy011 D R) ∉
      (((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCphi (Class.cv (nb096AlphaDummy006 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCphi (Class.cv (nb096AlphaDummy006 D R))))))).fv) :=
  by
  simpa only [nb096AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCphi (Class.cv (nb096AlphaDummy006 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCphi (Class.cv (nb096AlphaDummy006 D R))))))).fv)
      0

theorem nb096_fresh_001 (D : Class) (R : Class) :
    (nb096AlphaDummy035 D R) ∉
      (((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb096AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb096_fresh_002 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy036 D R q) ∉
      (((Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
              (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb096AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
              (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb096_fresh_003 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy012 D R q) ∉
      (((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCphi (Class.cv (nb096AlphaDummy008 D R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCphi (Class.cv (nb096AlphaDummy008 D R q))))))).fv) :=
  by
  simpa only [nb096AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCphi (Class.cv (nb096AlphaDummy008 D R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCphi (Class.cv (nb096AlphaDummy008 D R q))))))).fv)
      0

theorem nb096_fresh_004 (D : Class) (R : Class) :
    (nb096AlphaDummy095 D R) ∉
      (((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb096AlphaDummy095] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb096_fresh_005 (D : Class) (R : Class) :
    (nb096AlphaDummy071 D R) ∉
      (((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCphi (Class.cv (nb096AlphaDummy066 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCphi (Class.cv (nb096AlphaDummy066 D R))))))).fv) :=
  by
  simpa only [nb096AlphaDummy071] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCphi (Class.cv (nb096AlphaDummy066 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCphi (Class.cv (nb096AlphaDummy066 D R))))))).fv)
      0

theorem nb096_fresh_006 (R : Class) (q : Var) :
    (nb096AlphaDummy096 R q) ∉
      (((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb096AlphaDummy096] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb096_fresh_007 (R : Class) (q : Var) :
    (nb096AlphaDummy072 R q) ∉
      (((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCphi (Class.cv (nb096AlphaDummy068 R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCphi (Class.cv (nb096AlphaDummy068 R q))))))).fv) :=
  by
  simpa only [nb096AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCphi (Class.cv (nb096AlphaDummy068 R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCphi (Class.cv (nb096AlphaDummy068 R q))))))).fv)
      0

theorem nb096_fresh_008 (D : Class) (R : Class) :
    (nb096AlphaDummy131 D R) ∉
      (((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb096AlphaDummy131] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb096_fresh_009 (D : Class) (R : Class) :
    (nb096AlphaDummy107 D R) ∉
      (((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCphi (Class.cv (nb096AlphaDummy102 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCphi (Class.cv (nb096AlphaDummy102 D R))))))).fv) :=
  by
  simpa only [nb096AlphaDummy107] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCphi (Class.cv (nb096AlphaDummy102 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCphi (Class.cv (nb096AlphaDummy102 D R))))))).fv)
      0

theorem nb096_fresh_010 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy132 D R q) ∉
      (((Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy043 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy103 D R q)
            (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy043 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb096AlphaDummy132] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy043 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy103 D R q)
            (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy043 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb096_fresh_011 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy108 D R q) ∉
      (((Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy044 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCphi (Class.cv (nb096AlphaDummy104 D R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy044 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCphi (Class.cv (nb096AlphaDummy104 D R q))))))).fv) :=
  by
  simpa only [nb096AlphaDummy108] using
    freshVar_not_mem
      (((Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy044 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCphi (Class.cv (nb096AlphaDummy104 D R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy044 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCphi (Class.cv (nb096AlphaDummy104 D R q))))))).fv)
      0

theorem nb096_fresh_012 (D : Class) (R : Class) :
    (nb096AlphaDummy061 D R) ∉ (((Class.cv (nb096AlphaDummy000 D R))).fv) := by
  simpa only [nb096AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy000 D R))).fv) 0

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

theorem nb096_fresh_013 (D : Class) (R : Class) :
    (nb096AlphaDummy062 D R) ∉ (((Class.cv (nb096AlphaDummy000 D R))).fv) := by
  simpa only [nb096AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy000 D R))).fv) 1

theorem nb096_distinct_014 (D : Class) (R : Class) :
    (nb096AlphaDummy061 D R) ≠ (nb096AlphaDummy062 D R) := by
  simpa only [nb096AlphaDummy061, nb096AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy000 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_015 (D : Class) (R : Class) :
    (nb096AlphaDummy005 D R) ∉
      (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy001 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy001 D R))).fv)
      0

theorem nb096_fresh_016 (D : Class) (R : Class) :
    (nb096AlphaDummy006 D R) ∉
      (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy001 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy001 D R))).fv)
      1

theorem nb096_distinct_017 (D : Class) (R : Class) :
    (nb096AlphaDummy005 D R) ≠ (nb096AlphaDummy006 D R) := by
  simpa only [nb096AlphaDummy005, nb096AlphaDummy006] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy001 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_018 (D : Class) (R : Class) :
    (nb096AlphaDummy013 D R) ∉ (((Class.cv (nb096AlphaDummy006 D R))).fv) := by
  simpa only [nb096AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy006 D R))).fv) 0

theorem nb096_fresh_019 (D : Class) (R : Class) :
    (nb096AlphaDummy014 D R) ∉ (((Class.cv (nb096AlphaDummy006 D R))).fv) := by
  simpa only [nb096AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy006 D R))).fv) 1

theorem nb096_distinct_020 (D : Class) (R : Class) :
    (nb096AlphaDummy013 D R) ≠ (nb096AlphaDummy014 D R) := by
  simpa only [nb096AlphaDummy013, nb096AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy006 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_021 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy015 D R q) ∉ (((Class.cv (nb096AlphaDummy008 D R q))).fv) := by
  simpa only [nb096AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy008 D R q))).fv) 0

theorem nb096_fresh_022 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy016 D R q) ∉ (((Class.cv (nb096AlphaDummy008 D R q))).fv) := by
  simpa only [nb096AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy008 D R q))).fv) 1

theorem nb096_distinct_023 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy016 D R q) := by
  simpa only [nb096AlphaDummy015, nb096AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy008 D R q))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_024 (D : Class) (R : Class) :
    (nb096AlphaDummy019 D R) ∉
      (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 0

theorem nb096_fresh_025 (D : Class) (R : Class) :
    (nb096AlphaDummy020 D R) ∉
      (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 1

theorem nb096_fresh_026 (D : Class) (R : Class) :
    (nb096AlphaDummy021 D R) ∉
      (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 2

theorem nb096_distinct_027 (D : Class) (R : Class) :
    (nb096AlphaDummy019 D R) ≠ (nb096AlphaDummy020 D R) := by
  simpa only [nb096AlphaDummy019, nb096AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_028 (D : Class) (R : Class) :
    (nb096AlphaDummy019 D R) ≠ (nb096AlphaDummy021 D R) := by
  simpa only [nb096AlphaDummy019, nb096AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_029 (D : Class) (R : Class) :
    (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy021 D R) := by
  simpa only [nb096AlphaDummy020, nb096AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_030 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy022 D R q) ∉
      (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) 0

theorem nb096_fresh_031 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy023 D R q) ∉
      (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) 1

theorem nb096_fresh_032 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy024 D R q) ∉
      (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) 2

theorem nb096_distinct_033 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy022 D R q) ≠ (nb096AlphaDummy023 D R q) := by
  simpa only [nb096AlphaDummy022, nb096AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_034 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy022 D R q) ≠ (nb096AlphaDummy024 D R q) := by
  simpa only [nb096AlphaDummy022, nb096AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_035 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy024 D R q) := by
  simpa only [nb096AlphaDummy023, nb096AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_036 (D : Class) (R : Class) :
    (nb096AlphaDummy031 D R) ∉
      (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy020 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy020 D R))).fv)
      0

theorem nb096_fresh_037 (D : Class) (R : Class) :
    (nb096AlphaDummy027 D R) ∉
      (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy021 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy021 D R))).fv)
      0

theorem nb096_fresh_038 (D : Class) (R : Class) :
    (nb096AlphaDummy033 D R) ∉
      (((Class.cv (nb096AlphaDummy021 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy021 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy021 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy021 D R))).fv)
      0

theorem nb096_fresh_039 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy032 D R q) ∉
      (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy023 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy023 D R q))).fv)
      0

theorem nb096_fresh_040 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy028 D R q) ∉
      (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy024 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy024 D R q))).fv)
      0

theorem nb096_fresh_041 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy034 D R q) ∉
      (((Class.cv (nb096AlphaDummy024 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy024 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy024 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy024 D R q))).fv)
      0

theorem nb096_fresh_042 (D : Class) (R : Class) :
    (nb096AlphaDummy101 D R) ∉
      (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy041 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy101] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy041 D R))).fv)
      0

theorem nb096_fresh_043 (D : Class) (R : Class) :
    (nb096AlphaDummy102 D R) ∉
      (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy041 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy102] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy041 D R))).fv)
      1

theorem nb096_distinct_044 (D : Class) (R : Class) :
    (nb096AlphaDummy101 D R) ≠ (nb096AlphaDummy102 D R) := by
  simpa only [nb096AlphaDummy101, nb096AlphaDummy102] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy041 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_045 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy103 D R q) ∉
      (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy043 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy103] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy043 D R q))).fv)
      0

theorem nb096_fresh_046 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy104 D R q) ∉
      (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy043 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy104] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy043 D R q))).fv)
      1

theorem nb096_distinct_047 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy103 D R q) ≠ (nb096AlphaDummy104 D R q) := by
  simpa only [nb096AlphaDummy103, nb096AlphaDummy104] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy043 D R q))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_048 (D : Class) (R : Class) :
    (nb096AlphaDummy065 D R) ∉
      (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv)
      0

theorem nb096_fresh_049 (D : Class) (R : Class) :
    (nb096AlphaDummy066 D R) ∉
      (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy066] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv)
      1

theorem nb096_distinct_050 (D : Class) (R : Class) :
    (nb096AlphaDummy065 D R) ≠ (nb096AlphaDummy066 D R) := by
  simpa only [nb096AlphaDummy065, nb096AlphaDummy066] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_051 (R : Class) (q : Var) :
    (nb096AlphaDummy067 R q) ∉
      (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy053 R q))).fv) :=
  by
  simpa only [nb096AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy053 R q))).fv)
      0

theorem nb096_fresh_052 (R : Class) (q : Var) :
    (nb096AlphaDummy068 R q) ∉
      (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy053 R q))).fv) :=
  by
  simpa only [nb096AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy053 R q))).fv)
      1

theorem nb096_distinct_053 (R : Class) (q : Var) :
    (nb096AlphaDummy067 R q) ≠ (nb096AlphaDummy068 R q) := by
  simpa only [nb096AlphaDummy067, nb096AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy053 R q))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_054 (D : Class) (R : Class) :
    (nb096AlphaDummy073 D R) ∉ (((Class.cv (nb096AlphaDummy066 D R))).fv) := by
  simpa only [nb096AlphaDummy073] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy066 D R))).fv) 0

theorem nb096_fresh_055 (D : Class) (R : Class) :
    (nb096AlphaDummy074 D R) ∉ (((Class.cv (nb096AlphaDummy066 D R))).fv) := by
  simpa only [nb096AlphaDummy074] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy066 D R))).fv) 1

theorem nb096_distinct_056 (D : Class) (R : Class) :
    (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy074 D R) := by
  simpa only [nb096AlphaDummy073, nb096AlphaDummy074] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy066 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_057 (R : Class) (q : Var) :
    (nb096AlphaDummy075 R q) ∉ (((Class.cv (nb096AlphaDummy068 R q))).fv) := by
  simpa only [nb096AlphaDummy075] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy068 R q))).fv) 0

theorem nb096_fresh_058 (R : Class) (q : Var) :
    (nb096AlphaDummy076 R q) ∉ (((Class.cv (nb096AlphaDummy068 R q))).fv) := by
  simpa only [nb096AlphaDummy076] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy068 R q))).fv) 1

theorem nb096_distinct_059 (R : Class) (q : Var) :
    (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy076 R q) := by
  simpa only [nb096AlphaDummy075, nb096AlphaDummy076] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy068 R q))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_060 (D : Class) (R : Class) :
    (nb096AlphaDummy079 D R) ∉
      (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy079] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 0

theorem nb096_fresh_061 (D : Class) (R : Class) :
    (nb096AlphaDummy080 D R) ∉
      (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy080] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 1

theorem nb096_fresh_062 (D : Class) (R : Class) :
    (nb096AlphaDummy081 D R) ∉
      (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy081] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 2

theorem nb096_distinct_063 (D : Class) (R : Class) :
    (nb096AlphaDummy079 D R) ≠ (nb096AlphaDummy080 D R) := by
  simpa only [nb096AlphaDummy079, nb096AlphaDummy080] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_064 (D : Class) (R : Class) :
    (nb096AlphaDummy079 D R) ≠ (nb096AlphaDummy081 D R) := by
  simpa only [nb096AlphaDummy079, nb096AlphaDummy081] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_065 (D : Class) (R : Class) :
    (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy081 D R) := by
  simpa only [nb096AlphaDummy080, nb096AlphaDummy081] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_066 (R : Class) (q : Var) :
    (nb096AlphaDummy082 R q) ∉
      (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy082] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) 0

theorem nb096_fresh_067 (R : Class) (q : Var) :
    (nb096AlphaDummy083 R q) ∉
      (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy083] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) 1

theorem nb096_fresh_068 (R : Class) (q : Var) :
    (nb096AlphaDummy084 R q) ∉
      (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy084] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) 2

theorem nb096_distinct_069 (R : Class) (q : Var) :
    (nb096AlphaDummy082 R q) ≠ (nb096AlphaDummy083 R q) := by
  simpa only [nb096AlphaDummy082, nb096AlphaDummy083] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_070 (R : Class) (q : Var) :
    (nb096AlphaDummy082 R q) ≠ (nb096AlphaDummy084 R q) := by
  simpa only [nb096AlphaDummy082, nb096AlphaDummy084] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_071 (R : Class) (q : Var) :
    (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy084 R q) := by
  simpa only [nb096AlphaDummy083, nb096AlphaDummy084] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_072 (D : Class) (R : Class) :
    (nb096AlphaDummy091 D R) ∉
      (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy080 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy091] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy080 D R))).fv)
      0

theorem nb096_fresh_073 (D : Class) (R : Class) :
    (nb096AlphaDummy087 D R) ∉
      (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy081 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy087] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy081 D R))).fv)
      0

theorem nb096_fresh_074 (D : Class) (R : Class) :
    (nb096AlphaDummy093 D R) ∉
      (((Class.cv (nb096AlphaDummy081 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy081 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy093] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy081 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy081 D R))).fv)
      0

theorem nb096_fresh_075 (R : Class) (q : Var) :
    (nb096AlphaDummy092 R q) ∉
      (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy083 R q))).fv) :=
  by
  simpa only [nb096AlphaDummy092] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy083 R q))).fv)
      0

theorem nb096_fresh_076 (R : Class) (q : Var) :
    (nb096AlphaDummy088 R q) ∉
      (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy084 R q))).fv) :=
  by
  simpa only [nb096AlphaDummy088] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy084 R q))).fv)
      0

theorem nb096_fresh_077 (R : Class) (q : Var) :
    (nb096AlphaDummy094 R q) ∉
      (((Class.cv (nb096AlphaDummy084 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy084 R q))).fv) :=
  by
  simpa only [nb096AlphaDummy094] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy084 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy084 R q))).fv)
      0

theorem nb096_fresh_078 (D : Class) (R : Class) :
    (nb096AlphaDummy109 D R) ∉ (((Class.cv (nb096AlphaDummy102 D R))).fv) := by
  simpa only [nb096AlphaDummy109] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy102 D R))).fv) 0

theorem nb096_fresh_079 (D : Class) (R : Class) :
    (nb096AlphaDummy110 D R) ∉ (((Class.cv (nb096AlphaDummy102 D R))).fv) := by
  simpa only [nb096AlphaDummy110] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy102 D R))).fv) 1

theorem nb096_distinct_080 (D : Class) (R : Class) :
    (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy110 D R) := by
  simpa only [nb096AlphaDummy109, nb096AlphaDummy110] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy102 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_081 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy111 D R q) ∉ (((Class.cv (nb096AlphaDummy104 D R q))).fv) := by
  simpa only [nb096AlphaDummy111] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy104 D R q))).fv) 0

theorem nb096_fresh_082 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy112 D R q) ∉ (((Class.cv (nb096AlphaDummy104 D R q))).fv) := by
  simpa only [nb096AlphaDummy112] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy104 D R q))).fv) 1

theorem nb096_distinct_083 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy112 D R q) := by
  simpa only [nb096AlphaDummy111, nb096AlphaDummy112] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy104 D R q))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_084 (D : Class) (R : Class) :
    (nb096AlphaDummy115 D R) ∉
      (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy115] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) 0

theorem nb096_fresh_085 (D : Class) (R : Class) :
    (nb096AlphaDummy116 D R) ∉
      (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy116] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) 1

theorem nb096_fresh_086 (D : Class) (R : Class) :
    (nb096AlphaDummy117 D R) ∉
      (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy117] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) 2

theorem nb096_distinct_087 (D : Class) (R : Class) :
    (nb096AlphaDummy115 D R) ≠ (nb096AlphaDummy116 D R) := by
  simpa only [nb096AlphaDummy115, nb096AlphaDummy116] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_088 (D : Class) (R : Class) :
    (nb096AlphaDummy115 D R) ≠ (nb096AlphaDummy117 D R) := by
  simpa only [nb096AlphaDummy115, nb096AlphaDummy117] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_089 (D : Class) (R : Class) :
    (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy117 D R) := by
  simpa only [nb096AlphaDummy116, nb096AlphaDummy117] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_090 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy118 D R q) ∉
      (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy118] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) 0

theorem nb096_fresh_091 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy119 D R q) ∉
      (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy119] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) 1

theorem nb096_fresh_092 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy120 D R q) ∉
      (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb096AlphaDummy120] using
    freshVar_not_mem (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) 2

theorem nb096_distinct_093 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy118 D R q) ≠ (nb096AlphaDummy119 D R q) := by
  simpa only [nb096AlphaDummy118, nb096AlphaDummy119] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_094 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy118 D R q) ≠ (nb096AlphaDummy120 D R q) := by
  simpa only [nb096AlphaDummy118, nb096AlphaDummy120] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_095 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy120 D R q) := by
  simpa only [nb096AlphaDummy119, nb096AlphaDummy120] using
    (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_096 (D : Class) (R : Class) :
    (nb096AlphaDummy127 D R) ∉
      (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy116 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy127] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy116 D R))).fv)
      0

theorem nb096_fresh_097 (D : Class) (R : Class) :
    (nb096AlphaDummy123 D R) ∉
      (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy117 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy123] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy117 D R))).fv)
      0

theorem nb096_fresh_098 (D : Class) (R : Class) :
    (nb096AlphaDummy129 D R) ∉
      (((Class.cv (nb096AlphaDummy117 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy117 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy129] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy117 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy117 D R))).fv)
      0

theorem nb096_fresh_099 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy128 D R q) ∉
      (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy119 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy128] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy119 D R q))).fv)
      0

theorem nb096_fresh_100 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy124 D R q) ∉
      (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy120 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy124] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy120 D R q))).fv)
      0

theorem nb096_fresh_101 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy130 D R q) ∉
      (((Class.cv (nb096AlphaDummy120 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy120 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy130] using
    freshVar_not_mem
      (((Class.cv (nb096AlphaDummy120 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy120 D R q))).fv)
      0

theorem nb096_fresh_102 (q : Var) : (nb096AlphaDummy063 q) ∉ (((Class.cv q)).fv) := by
  simpa only [nb096AlphaDummy063] using freshVar_not_mem (((Class.cv q)).fv) 0

theorem nb096_fresh_103 (q : Var) : (nb096AlphaDummy064 q) ∉ (((Class.cv q)).fv) := by
  simpa only [nb096AlphaDummy064] using freshVar_not_mem (((Class.cv q)).fv) 1

theorem nb096_distinct_104 (q : Var) :
    (nb096AlphaDummy063 q) ≠ (nb096AlphaDummy064 q) := by
  simpa only [nb096AlphaDummy063, nb096AlphaDummy064] using
    (freshVar_injective (((Class.cv q)).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_105 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy007 D R q) ∉
      (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy007] using
    freshVar_not_mem (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) 0

theorem nb096_fresh_106 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy008 D R q) ∉
      (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy008] using
    freshVar_not_mem (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) 1

theorem nb096_distinct_107 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy007 D R q) ≠ (nb096AlphaDummy008 D R q) := by
  simpa only [nb096AlphaDummy007, nb096AlphaDummy008] using
    (freshVar_injective
      (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb096_fresh_108 (D : Class) (R : Class) :
    (nb096AlphaDummy017 D R) ∉
      (((Wff.classMem (Class.cv (nb096AlphaDummy013 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy013 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy013 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096AlphaDummy013 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy013 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy013 D R))).fv)
      0

theorem nb096_fresh_109 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy018 D R q) ∉
      (((Wff.classMem (Class.cv (nb096AlphaDummy015 D R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy015 D R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy015 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096AlphaDummy015 D R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy015 D R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy015 D R q))).fv)
      0

theorem nb096_fresh_110 (D : Class) (R : Class) :
    (nb096AlphaDummy077 D R) ∉
      (((Wff.classMem (Class.cv (nb096AlphaDummy073 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy073 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy073 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy077] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096AlphaDummy073 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy073 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy073 D R))).fv)
      0

theorem nb096_fresh_111 (R : Class) (q : Var) :
    (nb096AlphaDummy078 R q) ∉
      (((Wff.classMem (Class.cv (nb096AlphaDummy075 R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy075 R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy075 R q))).fv) :=
  by
  simpa only [nb096AlphaDummy078] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096AlphaDummy075 R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy075 R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy075 R q))).fv)
      0

theorem nb096_fresh_112 (D : Class) (R : Class) :
    (nb096AlphaDummy113 D R) ∉
      (((Wff.classMem (Class.cv (nb096AlphaDummy109 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy109 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy109 D R))).fv) :=
  by
  simpa only [nb096AlphaDummy113] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096AlphaDummy109 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy109 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy109 D R))).fv)
      0

theorem nb096_fresh_113 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy114 D R q) ∉
      (((Wff.classMem (Class.cv (nb096AlphaDummy111 D R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy111 D R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy111 D R q))).fv) :=
  by
  simpa only [nb096AlphaDummy114] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096AlphaDummy111 D R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy111 D R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy111 D R q))).fv)
      0

theorem nb096_fresh_114 (D : Class) (R : Class) :
    (nb096AlphaDummy051 D R) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv) :=
  by
  simpa only [nb096AlphaDummy051] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv)
      0

theorem nb096_fresh_115 (D : Class) (R : Class) :
    (nb096AlphaDummy052 D R) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv) :=
  by
  simpa only [nb096AlphaDummy052] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv)
      1

theorem nb096_distinct_116 (D : Class) (R : Class) :
    (nb096AlphaDummy051 D R) ≠ (nb096AlphaDummy052 D R) := by
  simpa only [nb096AlphaDummy051, nb096AlphaDummy052] using
    (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_fresh_117 (R : Class) (q : Var) :
    (nb096AlphaDummy053 R q) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv q))))).fv) :=
  by
  simpa only [nb096AlphaDummy053] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv q))))).fv)
      0

theorem nb096_fresh_118 (R : Class) (q : Var) :
    (nb096AlphaDummy054 R q) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv q))))).fv) :=
  by
  simpa only [nb096AlphaDummy054] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv q))))).fv)
      1

theorem nb096_distinct_119 (R : Class) (q : Var) :
    (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy054 R q) := by
  simpa only [nb096AlphaDummy053, nb096AlphaDummy054] using
    (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv q))))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_120 (D : Class) (R : Class) :
    (nb096AlphaDummy009 D R) ∉
      (((synCcompl (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCphi (Class.cv (nb096AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCphi (Class.cv (nb096AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb096_fresh_121 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy010 D R q) ∉
      (((synCcompl (Class.cab (nb096AlphaDummy007 D R q)
              (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCphi (Class.cv (nb096AlphaDummy008 D R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
                (Class.cv (nb096AlphaDummy002 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb096AlphaDummy007 D R q)
              (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCphi (Class.cv (nb096AlphaDummy008 D R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
                (Class.cv (nb096AlphaDummy002 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb096_fresh_122 (D : Class) (R : Class) :
    (nb096AlphaDummy069 D R) ∉
      (((synCcompl (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCphi (Class.cv (nb096AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy069] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCphi (Class.cv (nb096AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb096_fresh_123 (R : Class) (q : Var) :
    (nb096AlphaDummy070 R q) ∉
      (((synCcompl (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCphi (Class.cv (nb096AlphaDummy068 R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy070] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCphi (Class.cv (nb096AlphaDummy068 R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb096_fresh_124 (D : Class) (R : Class) :
    (nb096AlphaDummy105 D R) ∉
      (((synCcompl (Class.cab (nb096AlphaDummy101 D R)
              (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                  (synCphi (Class.cv (nb096AlphaDummy102 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy101 D R)
              (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy105] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb096AlphaDummy101 D R)
              (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                  (synCphi (Class.cv (nb096AlphaDummy102 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy101 D R)
              (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb096_fresh_125 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy106 D R q) ∉
      (((synCcompl (Class.cab (nb096AlphaDummy103 D R q)
              (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy044 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                  (synCphi (Class.cv (nb096AlphaDummy104 D R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
                (Class.cv (nb096AlphaDummy043 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy106] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb096AlphaDummy103 D R q)
              (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy044 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                  (synCphi (Class.cv (nb096AlphaDummy104 D R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
                (Class.cv (nb096AlphaDummy043 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb096_fresh_126 (D : Class) (R : Class) :
    (nb096AlphaDummy029 D R) ∉
      (((synCcompl (Class.cv (nb096AlphaDummy020 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy021 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb096AlphaDummy020 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy021 D R)))).fv)
      0

theorem nb096_fresh_127 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy030 D R q) ∉
      (((synCcompl (Class.cv (nb096AlphaDummy023 D R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy024 D R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb096AlphaDummy023 D R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy024 D R q)))).fv)
      0

theorem nb096_fresh_128 (D : Class) (R : Class) :
    (nb096AlphaDummy089 D R) ∉
      (((synCcompl (Class.cv (nb096AlphaDummy080 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy081 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy089] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb096AlphaDummy080 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy081 D R)))).fv)
      0

theorem nb096_fresh_129 (R : Class) (q : Var) :
    (nb096AlphaDummy090 R q) ∉
      (((synCcompl (Class.cv (nb096AlphaDummy083 R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy084 R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy090] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb096AlphaDummy083 R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy084 R q)))).fv)
      0

theorem nb096_fresh_130 (D : Class) (R : Class) :
    (nb096AlphaDummy125 D R) ∉
      (((synCcompl (Class.cv (nb096AlphaDummy116 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy117 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy125] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb096AlphaDummy116 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy117 D R)))).fv)
      0

theorem nb096_fresh_131 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy126 D R q) ∉
      (((synCcompl (Class.cv (nb096AlphaDummy119 D R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy120 D R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy126] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb096AlphaDummy119 D R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy120 D R q)))).fv)
      0

theorem nb096_fresh_132 (D : Class) (R : Class) :
    (nb096AlphaDummy037 D R) ∉
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy006 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb096AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy006 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb096_fresh_133 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy038 D R q) ∉
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy008 D R q))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb096AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy008 D R q))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb096_fresh_134 (D : Class) (R : Class) :
    (nb096AlphaDummy097 D R) ∉
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy066 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb096AlphaDummy097] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy066 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb096_fresh_135 (R : Class) (q : Var) :
    (nb096AlphaDummy098 R q) ∉
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy068 R q))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb096AlphaDummy098] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy068 R q))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb096_fresh_136 (D : Class) (R : Class) :
    (nb096AlphaDummy133 D R) ∉
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy102 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb096AlphaDummy133] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy102 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb096_fresh_137 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy134 D R q) ∉
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy104 D R q))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb096AlphaDummy134] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy104 D R q))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb096_fresh_138 (D : Class) (R : Class) :
    (nb096AlphaDummy041 D R) ∉
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv) :=
  by
  simpa only [nb096AlphaDummy041] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
      0

theorem nb096_fresh_139 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∉
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv) :=
  by
  simpa only [nb096AlphaDummy042] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
      1

theorem nb096_distinct_140 (D : Class) (R : Class) :
    (nb096AlphaDummy041 D R) ≠ (nb096AlphaDummy042 D R) := by
  simpa only [nb096AlphaDummy041, nb096AlphaDummy042] using
    (freshVar_injective (((synCen)).fv ∪ ((synCsn (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_fresh_141 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy043 D R q) ∉
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy043] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
      0

theorem nb096_fresh_142 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∉
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy044] using
    freshVar_not_mem
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
      1

theorem nb096_distinct_143 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy043 D R q) ≠ (nb096AlphaDummy044 D R q) := by
  simpa only [nb096AlphaDummy043, nb096AlphaDummy044] using
    (freshVar_injective (((synCen)).fv ∪ ((synCsn (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_fresh_144 (D : Class) (R : Class) :
    (nb096AlphaDummy045 D R) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
              (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy045] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv)
      0

theorem nb096_fresh_145 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy046 D R q) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q))))))).fv) :=
  by
  simpa only [nb096AlphaDummy046] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q))))))).fv)
      0

theorem nb096_fresh_146 (D : Class) (R : Class) :
    (nb096AlphaDummy025 D R) ∉
      (((synCnin (Class.cv (nb096AlphaDummy020 D R))
            (Class.cv (nb096AlphaDummy021 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy020 D R))
            (Class.cv (nb096AlphaDummy021 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb096AlphaDummy020 D R))
            (Class.cv (nb096AlphaDummy021 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy020 D R))
            (Class.cv (nb096AlphaDummy021 D R)))).fv)
      0

theorem nb096_fresh_147 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy026 D R q) ∉
      (((synCnin (Class.cv (nb096AlphaDummy023 D R q))
            (Class.cv (nb096AlphaDummy024 D R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy023 D R q))
            (Class.cv (nb096AlphaDummy024 D R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb096AlphaDummy023 D R q))
            (Class.cv (nb096AlphaDummy024 D R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy023 D R q))
            (Class.cv (nb096AlphaDummy024 D R q)))).fv)
      0

theorem nb096_fresh_148 (D : Class) (R : Class) :
    (nb096AlphaDummy085 D R) ∉
      (((synCnin (Class.cv (nb096AlphaDummy080 D R))
            (Class.cv (nb096AlphaDummy081 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy080 D R))
            (Class.cv (nb096AlphaDummy081 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy085] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb096AlphaDummy080 D R))
            (Class.cv (nb096AlphaDummy081 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy080 D R))
            (Class.cv (nb096AlphaDummy081 D R)))).fv)
      0

theorem nb096_fresh_149 (R : Class) (q : Var) :
    (nb096AlphaDummy086 R q) ∉
      (((synCnin (Class.cv (nb096AlphaDummy083 R q))
            (Class.cv (nb096AlphaDummy084 R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy083 R q))
            (Class.cv (nb096AlphaDummy084 R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy086] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb096AlphaDummy083 R q))
            (Class.cv (nb096AlphaDummy084 R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy083 R q))
            (Class.cv (nb096AlphaDummy084 R q)))).fv)
      0

theorem nb096_fresh_150 (D : Class) (R : Class) :
    (nb096AlphaDummy121 D R) ∉
      (((synCnin (Class.cv (nb096AlphaDummy116 D R))
            (Class.cv (nb096AlphaDummy117 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy116 D R))
            (Class.cv (nb096AlphaDummy117 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy121] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb096AlphaDummy116 D R))
            (Class.cv (nb096AlphaDummy117 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy116 D R))
            (Class.cv (nb096AlphaDummy117 D R)))).fv)
      0

theorem nb096_fresh_151 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy122 D R q) ∉
      (((synCnin (Class.cv (nb096AlphaDummy119 D R q))
            (Class.cv (nb096AlphaDummy120 D R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy119 D R q))
            (Class.cv (nb096AlphaDummy120 D R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy122] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb096AlphaDummy119 D R q))
            (Class.cv (nb096AlphaDummy120 D R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy119 D R q))
            (Class.cv (nb096AlphaDummy120 D R q)))).fv)
      0

theorem nb096_fresh_152 (D : Class) (R : Class) :
    (nb096AlphaDummy047 D R) ∉
      (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv ∪
        ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy047] using
    freshVar_not_mem
      (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv ∪
        ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv)
      0

theorem nb096_fresh_153 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy048 D R q) ∉
      (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))).fv ∪ ((synCnin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))).fv) :=
  by
  simpa only [nb096AlphaDummy048] using
    freshVar_not_mem
      (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))).fv ∪ ((synCnin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))).fv)
      0

theorem nb096_fresh_154 (D : Class) (R : Class) :
    (nb096AlphaDummy039 D R) ∉
      (((synCphi (Class.cv (nb096AlphaDummy006 D R)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy006 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb096AlphaDummy006 D R)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy006 D R)))).fv)
      0

theorem nb096_fresh_155 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy040 D R q) ∉
      (((synCphi (Class.cv (nb096AlphaDummy008 D R q)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy008 D R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb096AlphaDummy008 D R q)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy008 D R q)))).fv)
      0

theorem nb096_fresh_156 (D : Class) (R : Class) :
    (nb096AlphaDummy099 D R) ∉
      (((synCphi (Class.cv (nb096AlphaDummy066 D R)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy066 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy099] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb096AlphaDummy066 D R)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy066 D R)))).fv)
      0

theorem nb096_fresh_157 (R : Class) (q : Var) :
    (nb096AlphaDummy100 R q) ∉
      (((synCphi (Class.cv (nb096AlphaDummy068 R q)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy068 R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy100] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb096AlphaDummy068 R q)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy068 R q)))).fv)
      0

theorem nb096_fresh_158 (D : Class) (R : Class) :
    (nb096AlphaDummy135 D R) ∉
      (((synCphi (Class.cv (nb096AlphaDummy102 D R)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy102 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy135] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb096AlphaDummy102 D R)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy102 D R)))).fv)
      0

theorem nb096_fresh_159 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy136 D R q) ∉
      (((synCphi (Class.cv (nb096AlphaDummy104 D R q)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy104 D R q)))).fv) :=
  by
  simpa only [nb096AlphaDummy136] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb096AlphaDummy104 D R q)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy104 D R q)))).fv)
      0

theorem nb096_fresh_160 (D : Class) (R : Class) :
    (nb096AlphaDummy057 D R) ∉
      (((synCuni (Class.cv (nb096AlphaDummy000 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy057] using
    freshVar_not_mem (((synCuni (Class.cv (nb096AlphaDummy000 D R)))).fv) 0

theorem nb096_fresh_161 (D : Class) (R : Class) :
    (nb096AlphaDummy058 D R) ∉
      (((synCuni (Class.cv (nb096AlphaDummy000 D R)))).fv) :=
  by
  simpa only [nb096AlphaDummy058] using
    freshVar_not_mem (((synCuni (Class.cv (nb096AlphaDummy000 D R)))).fv) 1

theorem nb096_distinct_162 (D : Class) (R : Class) :
    (nb096AlphaDummy057 D R) ≠ (nb096AlphaDummy058 D R) := by
  simpa only [nb096AlphaDummy057, nb096AlphaDummy058] using
    (freshVar_injective (((synCuni (Class.cv (nb096AlphaDummy000 D R)))).fv) (i := 0)
      (j := 1) (by decide))

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

theorem nb096_fresh_163 (q : Var) :
    (nb096AlphaDummy059 q) ∉ (((synCuni (Class.cv q))).fv) := by
  simpa only [nb096AlphaDummy059] using
    freshVar_not_mem (((synCuni (Class.cv q))).fv) 0

theorem nb096_fresh_164 (q : Var) :
    (nb096AlphaDummy060 q) ∉ (((synCuni (Class.cv q))).fv) := by
  simpa only [nb096AlphaDummy060] using
    freshVar_not_mem (((synCuni (Class.cv q))).fv) 1

theorem nb096_distinct_165 (q : Var) :
    (nb096AlphaDummy059 q) ≠ (nb096AlphaDummy060 q) := by
  simpa only [nb096AlphaDummy059, nb096AlphaDummy060] using
    (freshVar_injective (((synCuni (Class.cv q))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_166 (D : Class) (R : Class) :
    (nb096AlphaDummy055 D R) ∉
      (((synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))).fv) :=
  by
  simpa only [nb096AlphaDummy055] using
    freshVar_not_mem (((synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))).fv) 0

theorem nb096_fresh_167 (q : Var) :
    (nb096AlphaDummy056 q) ∉ (((synCuni (synCuni (Class.cv q)))).fv) := by
  simpa only [nb096AlphaDummy056] using
    freshVar_not_mem (((synCuni (synCuni (Class.cv q)))).fv) 0

theorem nb096_fresh_168 (D : Class) (R : Class) :
    (nb096AlphaDummy049 D R) ∉
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid))) (synCsn
              (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))).fv) :=
  by
  simpa only [nb096AlphaDummy049] using
    freshVar_not_mem
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))).fv)
      0

theorem nb096_fresh_169 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy050 D R q) ∉
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q)))))).fv) :=
  by
  simpa only [nb096AlphaDummy050] using
    freshVar_not_mem
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q)))))).fv)
      0

theorem nb096_fresh_170 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∉ ((R).fv ∪ (D).fv) := by
  simpa only [nb096AlphaDummy000] using freshVar_not_mem ((R).fv ∪ (D).fv) 0

theorem nb096_fresh_171 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∉
      (({(nb096AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv) :=
  by
  simpa only [nb096AlphaDummy001] using
    freshVar_not_mem
      (({(nb096AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
      0

theorem nb096_fresh_172 (D : Class) (R : Class) :
    (nb096AlphaDummy003 D R) ∉
      (({(nb096AlphaDummy000 D R)} : Finset Var) ∪
          ({(nb096AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))))).fv) :=
  by
  simpa only [nb096AlphaDummy003] using
    freshVar_not_mem
      (({(nb096AlphaDummy000 D R)} : Finset Var) ∪
          ({(nb096AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))))).fv)
      0

theorem nb096_fresh_173 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∉
      (({ q } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) :=
  by
  simpa only [nb096AlphaDummy002] using
    freshVar_not_mem
      (({ q } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
      0

theorem nb096_fresh_174 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy004 D R q) ∉
      (({ q } : Finset Var) ∪ ({(nb096AlphaDummy002 D R q)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv q)))))))))).fv) :=
  by
  simpa only [nb096AlphaDummy004] using
    freshVar_not_mem
      (({ q } : Finset Var) ∪ ({(nb096AlphaDummy002 D R q)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv q)))))))))).fv)
      0

theorem nb096_support_mem_0000 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (({(nb096AlphaDummy000 D R)} : Finset Var) ∪
          ({(nb096AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0001 (D : Class) (R : Class) (q : Var) :
    q ∈
      (({ q } : Finset Var) ∪ ({(nb096AlphaDummy002 D R q)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv q)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0002 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∈
      (({(nb096AlphaDummy000 D R)} : Finset Var) ∪
          ({(nb096AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0003 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∈
      (({ q } : Finset Var) ∪ ({(nb096AlphaDummy002 D R q)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv q)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0004 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (({(nb096AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0005 (D : Class) (R : Class) (q : Var) :
    q ∈
      (({ q } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0006 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy001 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0007 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCphi (Class.cv (nb096AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy000 D R) ≠ (nb096AlphaDummy005 D R) from (by
          unfold nb096AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy000 D R) ≠ (nb096AlphaDummy006 D R) from (by
            unfold nb096AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0008 (D : Class) (R : Class) (q : Var) :
    q ∈ (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0009 (D : Class) (R : Class) (q : Var) :
    q ∈
      (((synCcompl (Class.cab (nb096AlphaDummy007 D R q)
              (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCphi (Class.cv (nb096AlphaDummy008 D R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
                (Class.cv (nb096AlphaDummy002 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show q ≠ (nb096AlphaDummy007 D R q) from (by
          unfold nb096AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show q ≠ (nb096AlphaDummy008 D R q) from (by
            unfold nb096AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0010 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCphi (Class.cv (nb096AlphaDummy006 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCphi (Class.cv (nb096AlphaDummy006 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy000 D R) ≠ (nb096AlphaDummy005 D R) from (by
          unfold nb096AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy000 D R) ≠ (nb096AlphaDummy006 D R) from (by
            unfold nb096AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0011 (D : Class) (R : Class) (q : Var) :
    q ∈
      (((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCphi (Class.cv (nb096AlphaDummy008 D R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCphi (Class.cv (nb096AlphaDummy008 D R q))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show q ≠ (nb096AlphaDummy007 D R q) from (by
          unfold nb096AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show q ≠ (nb096AlphaDummy008 D R q) from (by
            unfold nb096AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0012 (D : Class) (R : Class) :
    (nb096AlphaDummy006 D R) ∈ (((Class.cv (nb096AlphaDummy006 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0013 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy008 D R q) ∈ (((Class.cv (nb096AlphaDummy008 D R q))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0014 (D : Class) (R : Class) :
    (nb096AlphaDummy013 D R) ∈
      (((Wff.classMem (Class.cv (nb096AlphaDummy013 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy013 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy013 D R))).fv) :=
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

theorem nb096_support_mem_0015 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy015 D R q) ∈
      (((Wff.classMem (Class.cv (nb096AlphaDummy015 D R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy015 D R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy015 D R q))).fv) :=
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

theorem nb096_support_mem_0016 (D : Class) (R : Class) :
    (nb096AlphaDummy013 D R) ∈
      (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0017 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy015 D R q) ∈
      (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0018 (D : Class) (R : Class) :
    (nb096AlphaDummy020 D R) ∈
      (((synCnin (Class.cv (nb096AlphaDummy020 D R))
            (Class.cv (nb096AlphaDummy021 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy020 D R))
            (Class.cv (nb096AlphaDummy021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0019 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy023 D R q) ∈
      (((synCnin (Class.cv (nb096AlphaDummy023 D R q))
            (Class.cv (nb096AlphaDummy024 D R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy023 D R q))
            (Class.cv (nb096AlphaDummy024 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0020 (D : Class) (R : Class) :
    (nb096AlphaDummy020 D R) ∈
      (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0021 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy023 D R q) ∈
      (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy024 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0022 (D : Class) (R : Class) :
    (nb096AlphaDummy021 D R) ∈
      (((synCnin (Class.cv (nb096AlphaDummy020 D R))
            (Class.cv (nb096AlphaDummy021 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy020 D R))
            (Class.cv (nb096AlphaDummy021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0023 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy024 D R q) ∈
      (((synCnin (Class.cv (nb096AlphaDummy023 D R q))
            (Class.cv (nb096AlphaDummy024 D R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy023 D R q))
            (Class.cv (nb096AlphaDummy024 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0024 (D : Class) (R : Class) :
    (nb096AlphaDummy021 D R) ∈
      (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0025 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy024 D R q) ∈
      (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy024 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0026 (D : Class) (R : Class) :
    (nb096AlphaDummy020 D R) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy020 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0027 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy023 D R q) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy023 D R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy024 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0028 (D : Class) (R : Class) :
    (nb096AlphaDummy020 D R) ∈
      (((Class.cv (nb096AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy020 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0029 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy023 D R q) ∈
      (((Class.cv (nb096AlphaDummy023 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy023 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0030 (D : Class) (R : Class) :
    (nb096AlphaDummy021 D R) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy020 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0031 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy024 D R q) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy023 D R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy024 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0032 (D : Class) (R : Class) :
    (nb096AlphaDummy021 D R) ∈
      (((Class.cv (nb096AlphaDummy021 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0033 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy024 D R q) ∈
      (((Class.cv (nb096AlphaDummy024 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy024 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0034 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∈
      (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy001 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0035 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy000 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCphi (Class.cv (nb096AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy005 D R) from (by
          unfold nb096AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy006 D R) from (by
            unfold nb096AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0036 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∈
      (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0037 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy007 D R q)
              (synWrex (nb096AlphaDummy008 D R q) (Class.cv q)
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCphi (Class.cv (nb096AlphaDummy008 D R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
                (Class.cv (nb096AlphaDummy002 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy007 D R q) from (by
          unfold nb096AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy008 D R q) from (by
            unfold nb096AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0038 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∈
      (((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy005 D R) from (by
          unfold nb096AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy006 D R) from (by
            unfold nb096AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0039 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∈
      (((Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
              (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy007 D R q)
            (synWrex (nb096AlphaDummy008 D R q) (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy007 D R q) from (by
          unfold nb096AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy008 D R q) from (by
            unfold nb096AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0040 (D : Class) (R : Class) :
    (nb096AlphaDummy006 D R) ∈
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy006 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0041 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy008 D R q) ∈
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy008 D R q))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0042 (D : Class) (R : Class) :
    (nb096AlphaDummy006 D R) ∈
      (((synCphi (Class.cv (nb096AlphaDummy006 D R)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy006 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0043 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy008 D R q) ∈
      (((synCphi (Class.cv (nb096AlphaDummy008 D R q)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy008 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0044 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0045 (D : Class) (R : Class) (q : Var) :
    q ∈
      (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0046 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
              (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv) :=
  by
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0047 (D : Class) (R : Class) (q : Var) :
    q ∈
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q))))))).fv) :=
  by
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0048 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv ∪
        ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0049 (D : Class) (R : Class) (q : Var) :
    q ∈
      (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))).fv ∪ ((synCnin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0050 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid))) (synCsn
              (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0051 (D : Class) (R : Class) (q : Var) :
    q ∈
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0052 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0053 (R : Class) (q : Var) :
    q ∈
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv q))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0054 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0055 (q : Var) :
    q ∈ (((synCuni (synCuni (Class.cv q)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0056 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈
      (((synCuni (Class.cv (nb096AlphaDummy000 D R)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0057 (q : Var) : q ∈ (((synCuni (Class.cv q))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0058 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∈ (((Class.cv (nb096AlphaDummy000 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0059 (q : Var) : q ∈ (((Class.cv q)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0060 (D : Class) (R : Class) :
    (nb096AlphaDummy052 D R) ∈
      (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0061 (D : Class) (R : Class) :
    (nb096AlphaDummy052 D R) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCphi (Class.cv (nb096AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy065 D R) from (by
          unfold nb096AlphaDummy065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy066 D R) from (by
            unfold nb096AlphaDummy066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0062 (R : Class) (q : Var) :
    (nb096AlphaDummy054 R q) ∈
      (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy053 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0063 (R : Class) (q : Var) :
    (nb096AlphaDummy054 R q) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCphi (Class.cv (nb096AlphaDummy068 R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy067 R q) from (by
          unfold nb096AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy068 R q) from (by
            unfold nb096AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0064 (D : Class) (R : Class) :
    (nb096AlphaDummy052 D R) ∈
      (((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCphi (Class.cv (nb096AlphaDummy066 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCphi (Class.cv (nb096AlphaDummy066 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy065 D R) from (by
          unfold nb096AlphaDummy065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy066 D R) from (by
            unfold nb096AlphaDummy066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0065 (R : Class) (q : Var) :
    (nb096AlphaDummy054 R q) ∈
      (((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCphi (Class.cv (nb096AlphaDummy068 R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCphi (Class.cv (nb096AlphaDummy068 R q))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy067 R q) from (by
          unfold nb096AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy068 R q) from (by
            unfold nb096AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0066 (D : Class) (R : Class) :
    (nb096AlphaDummy066 D R) ∈ (((Class.cv (nb096AlphaDummy066 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0067 (R : Class) (q : Var) :
    (nb096AlphaDummy068 R q) ∈ (((Class.cv (nb096AlphaDummy068 R q))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0068 (D : Class) (R : Class) :
    (nb096AlphaDummy073 D R) ∈
      (((Wff.classMem (Class.cv (nb096AlphaDummy073 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy073 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy073 D R))).fv) :=
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

theorem nb096_support_mem_0069 (R : Class) (q : Var) :
    (nb096AlphaDummy075 R q) ∈
      (((Wff.classMem (Class.cv (nb096AlphaDummy075 R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy075 R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy075 R q))).fv) :=
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

theorem nb096_support_mem_0070 (D : Class) (R : Class) :
    (nb096AlphaDummy073 D R) ∈
      (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0071 (R : Class) (q : Var) :
    (nb096AlphaDummy075 R q) ∈
      (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0072 (D : Class) (R : Class) :
    (nb096AlphaDummy080 D R) ∈
      (((synCnin (Class.cv (nb096AlphaDummy080 D R))
            (Class.cv (nb096AlphaDummy081 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy080 D R))
            (Class.cv (nb096AlphaDummy081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0073 (R : Class) (q : Var) :
    (nb096AlphaDummy083 R q) ∈
      (((synCnin (Class.cv (nb096AlphaDummy083 R q))
            (Class.cv (nb096AlphaDummy084 R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy083 R q))
            (Class.cv (nb096AlphaDummy084 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0074 (D : Class) (R : Class) :
    (nb096AlphaDummy080 D R) ∈
      (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0075 (R : Class) (q : Var) :
    (nb096AlphaDummy083 R q) ∈
      (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy084 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0076 (D : Class) (R : Class) :
    (nb096AlphaDummy081 D R) ∈
      (((synCnin (Class.cv (nb096AlphaDummy080 D R))
            (Class.cv (nb096AlphaDummy081 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy080 D R))
            (Class.cv (nb096AlphaDummy081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0077 (R : Class) (q : Var) :
    (nb096AlphaDummy084 R q) ∈
      (((synCnin (Class.cv (nb096AlphaDummy083 R q))
            (Class.cv (nb096AlphaDummy084 R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy083 R q))
            (Class.cv (nb096AlphaDummy084 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0078 (D : Class) (R : Class) :
    (nb096AlphaDummy081 D R) ∈
      (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0079 (R : Class) (q : Var) :
    (nb096AlphaDummy084 R q) ∈
      (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy084 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0080 (D : Class) (R : Class) :
    (nb096AlphaDummy080 D R) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy080 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0081 (R : Class) (q : Var) :
    (nb096AlphaDummy083 R q) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy083 R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy084 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0082 (D : Class) (R : Class) :
    (nb096AlphaDummy080 D R) ∈
      (((Class.cv (nb096AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy080 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0083 (R : Class) (q : Var) :
    (nb096AlphaDummy083 R q) ∈
      (((Class.cv (nb096AlphaDummy083 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy083 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0084 (D : Class) (R : Class) :
    (nb096AlphaDummy081 D R) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy080 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0085 (R : Class) (q : Var) :
    (nb096AlphaDummy084 R q) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy083 R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy084 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0086 (D : Class) (R : Class) :
    (nb096AlphaDummy081 D R) ∈
      (((Class.cv (nb096AlphaDummy081 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0087 (R : Class) (q : Var) :
    (nb096AlphaDummy084 R q) ∈
      (((Class.cv (nb096AlphaDummy084 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy084 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0088 (D : Class) (R : Class) :
    (nb096AlphaDummy051 D R) ∈
      (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0089 (D : Class) (R : Class) :
    (nb096AlphaDummy051 D R) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCphi (Class.cv (nb096AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy051 D R) ≠ (nb096AlphaDummy065 D R) from (by
          unfold nb096AlphaDummy065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0088 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy051 D R) ≠ (nb096AlphaDummy066 D R) from (by
            unfold nb096AlphaDummy066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0088 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0090 (R : Class) (q : Var) :
    (nb096AlphaDummy053 R q) ∈
      (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
        ((Class.cv (nb096AlphaDummy053 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0091 (R : Class) (q : Var) :
    (nb096AlphaDummy053 R q) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCphi (Class.cv (nb096AlphaDummy068 R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy067 R q) from (by
          unfold nb096AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0090 R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy068 R q) from (by
            unfold nb096AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0090 R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0092 (D : Class) (R : Class) :
    (nb096AlphaDummy051 D R) ∈
      (((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy051 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy051 D R) ≠ (nb096AlphaDummy065 D R) from (by
          unfold nb096AlphaDummy065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0088 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy051 D R) ≠ (nb096AlphaDummy066 D R) from (by
            unfold nb096AlphaDummy066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0088 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0093 (R : Class) (q : Var) :
    (nb096AlphaDummy053 R q) ∈
      (((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy053 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy068 R q)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy067 R q) from (by
          unfold nb096AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0090 R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy068 R q) from (by
            unfold nb096AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0090 R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0094 (D : Class) (R : Class) :
    (nb096AlphaDummy066 D R) ∈
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy066 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0095 (R : Class) (q : Var) :
    (nb096AlphaDummy068 R q) ∈
      (((synCcompl (synCphi (Class.cv (nb096AlphaDummy068 R q))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0096 (D : Class) (R : Class) :
    (nb096AlphaDummy066 D R) ∈
      (((synCphi (Class.cv (nb096AlphaDummy066 D R)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy066 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0097 (R : Class) (q : Var) :
    (nb096AlphaDummy068 R q) ∈
      (((synCphi (Class.cv (nb096AlphaDummy068 R q)))).fv ∪
        ((synCphi (Class.cv (nb096AlphaDummy068 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0098 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∈
      (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy041 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0099 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy101 D R)
              (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                  (synCphi (Class.cv (nb096AlphaDummy102 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy101 D R)
              (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy041 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy101 D R) from (by
          unfold nb096AlphaDummy101;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0098 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy102 D R) from (by
            unfold nb096AlphaDummy102;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0098 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0100 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∈
      (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy043 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0101 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∈
      (((synCcompl (Class.cab (nb096AlphaDummy103 D R q)
              (synWrex (nb096AlphaDummy104 D R q) (Class.cv (nb096AlphaDummy044 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                  (synCphi (Class.cv (nb096AlphaDummy104 D R q)))))))).fv ∪ ((synCcompl
            (Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
                (Class.cv (nb096AlphaDummy043 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy044 D R q) ≠ (nb096AlphaDummy103 D R q) from (by
          unfold nb096AlphaDummy103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0100 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy044 D R q) ≠ (nb096AlphaDummy104 D R q) from (by
            unfold nb096AlphaDummy104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0100 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0102 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∈
      (((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCphi (Class.cv (nb096AlphaDummy102 D R))))))).fv ∪
        ((Class.cab (nb096AlphaDummy101 D R)
            (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                (synCphi (Class.cv (nb096AlphaDummy102 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy101 D R) from (by
          unfold nb096AlphaDummy101;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0098 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy102 D R) from (by
            unfold nb096AlphaDummy102;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0098 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0103 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∈
      (((Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy044 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCphi (Class.cv (nb096AlphaDummy104 D R q))))))).fv ∪
        ((Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
              (Class.cv (nb096AlphaDummy044 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                (synCphi (Class.cv (nb096AlphaDummy104 D R q))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096AlphaDummy044 D R q) ≠ (nb096AlphaDummy103 D R q) from (by
          unfold nb096AlphaDummy103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0100 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096AlphaDummy044 D R q) ≠ (nb096AlphaDummy104 D R q) from (by
            unfold nb096AlphaDummy104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0100 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0104 (D : Class) (R : Class) :
    (nb096AlphaDummy102 D R) ∈ (((Class.cv (nb096AlphaDummy102 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0105 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy104 D R q) ∈ (((Class.cv (nb096AlphaDummy104 D R q))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0106 (D : Class) (R : Class) :
    (nb096AlphaDummy109 D R) ∈
      (((Wff.classMem (Class.cv (nb096AlphaDummy109 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy109 D R)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy109 D R))).fv) :=
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

theorem nb096_support_mem_0107 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy111 D R q) ∈
      (((Wff.classMem (Class.cv (nb096AlphaDummy111 D R q)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb096AlphaDummy111 D R q)) (synC1c))).fv ∪
        ((Class.cv (nb096AlphaDummy111 D R q))).fv) :=
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

theorem nb096_support_mem_0108 (D : Class) (R : Class) :
    (nb096AlphaDummy109 D R) ∈
      (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0109 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy111 D R q) ∈
      (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0110 (D : Class) (R : Class) :
    (nb096AlphaDummy116 D R) ∈
      (((synCnin (Class.cv (nb096AlphaDummy116 D R))
            (Class.cv (nb096AlphaDummy117 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy116 D R))
            (Class.cv (nb096AlphaDummy117 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0111 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy119 D R q) ∈
      (((synCnin (Class.cv (nb096AlphaDummy119 D R q))
            (Class.cv (nb096AlphaDummy120 D R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy119 D R q))
            (Class.cv (nb096AlphaDummy120 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0112 (D : Class) (R : Class) :
    (nb096AlphaDummy116 D R) ∈
      (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy117 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0113 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy119 D R q) ∈
      (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy120 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0114 (D : Class) (R : Class) :
    (nb096AlphaDummy117 D R) ∈
      (((synCnin (Class.cv (nb096AlphaDummy116 D R))
            (Class.cv (nb096AlphaDummy117 D R)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy116 D R))
            (Class.cv (nb096AlphaDummy117 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0115 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy120 D R q) ∈
      (((synCnin (Class.cv (nb096AlphaDummy119 D R q))
            (Class.cv (nb096AlphaDummy120 D R q)))).fv ∪
        ((synCnin (Class.cv (nb096AlphaDummy119 D R q))
            (Class.cv (nb096AlphaDummy120 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0116 (D : Class) (R : Class) :
    (nb096AlphaDummy117 D R) ∈
      (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy117 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0117 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy120 D R q) ∈
      (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy120 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0118 (D : Class) (R : Class) :
    (nb096AlphaDummy116 D R) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy116 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy117 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0119 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy119 D R q) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy119 D R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy120 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0120 (D : Class) (R : Class) :
    (nb096AlphaDummy116 D R) ∈
      (((Class.cv (nb096AlphaDummy116 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy116 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0121 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy119 D R q) ∈
      (((Class.cv (nb096AlphaDummy119 D R q))).fv ∪
        ((Class.cv (nb096AlphaDummy119 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0122 (D : Class) (R : Class) :
    (nb096AlphaDummy117 D R) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy116 D R)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy117 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0123 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy120 D R q) ∈
      (((synCcompl (Class.cv (nb096AlphaDummy119 D R q)))).fv ∪
        ((synCcompl (Class.cv (nb096AlphaDummy120 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
