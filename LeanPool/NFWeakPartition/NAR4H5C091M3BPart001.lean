/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4H5C091M3BPart001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_000`. -/
@[expose]
noncomputable def nb091AlphaDummy000 (D : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_001`. -/
@[expose]
noncomputable def nb091AlphaDummy001 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb091AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪
      ((synCec (synChnwcutcode R D
            (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))) (synChwniso D))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_002`. -/
@[expose]
noncomputable def nb091AlphaDummy002 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (({ p } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪
      ((synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))) (synChwniso D))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_003`. -/
@[expose]
noncomputable def nb091AlphaDummy003 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb091AlphaDummy000 D R)} : Finset Var) ∪
        ({(nb091AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
          (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
              (synChwniso D))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_004`. -/
@[expose]
noncomputable def nb091AlphaDummy004 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (({ p } : Finset Var) ∪ ({(nb091AlphaDummy002 D R p)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
          (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
            (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
              (synChwniso D))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_005`. -/
@[expose]
noncomputable def nb091AlphaDummy005 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy001 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_006`. -/
@[expose]
noncomputable def nb091AlphaDummy006 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy001 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_007`. -/
@[expose]
noncomputable def nb091AlphaDummy007 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_008`. -/
@[expose]
noncomputable def nb091AlphaDummy008 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_009`. -/
@[expose]
noncomputable def nb091AlphaDummy009 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCphi (Class.cv (nb091AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_010`. -/
@[expose]
noncomputable def nb091AlphaDummy010 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCphi (Class.cv (nb091AlphaDummy008 D R p)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
              (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_011`. -/
@[expose]
noncomputable def nb091AlphaDummy011 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy005 D R)
          (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
              (synCphi (Class.cv (nb091AlphaDummy006 D R))))))).fv ∪
      ((Class.cab (nb091AlphaDummy005 D R)
          (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
              (synCphi (Class.cv (nb091AlphaDummy006 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_012`. -/
@[expose]
noncomputable def nb091AlphaDummy012 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy007 D R p)
          (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
            (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
              (synCphi (Class.cv (nb091AlphaDummy008 D R p))))))).fv ∪
      ((Class.cab (nb091AlphaDummy007 D R p)
          (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
            (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
              (synCphi (Class.cv (nb091AlphaDummy008 D R p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_013`. -/
@[expose]
noncomputable def nb091AlphaDummy013 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy006 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_014`. -/
@[expose]
noncomputable def nb091AlphaDummy014 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy006 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_015`. -/
@[expose]
noncomputable def nb091AlphaDummy015 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy008 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_016`. -/
@[expose]
noncomputable def nb091AlphaDummy016 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy008 D R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_017`. -/
@[expose]
noncomputable def nb091AlphaDummy017 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy013 D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy013 D R)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy013 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_018`. -/
@[expose]
noncomputable def nb091AlphaDummy018 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy015 D R p)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy015 D R p)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy015 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_019`. -/
@[expose]
noncomputable def nb091AlphaDummy019 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_020`. -/
@[expose]
noncomputable def nb091AlphaDummy020 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_021`. -/
@[expose]
noncomputable def nb091AlphaDummy021 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_022`. -/
@[expose]
noncomputable def nb091AlphaDummy022 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_023`. -/
@[expose]
noncomputable def nb091AlphaDummy023 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_024`. -/
@[expose]
noncomputable def nb091AlphaDummy024 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_025`. -/
@[expose]
noncomputable def nb091AlphaDummy025 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy020 D R))
          (Class.cv (nb091AlphaDummy021 D R)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy020 D R))
          (Class.cv (nb091AlphaDummy021 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_026`. -/
@[expose]
noncomputable def nb091AlphaDummy026 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy023 D R p))
          (Class.cv (nb091AlphaDummy024 D R p)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy023 D R p))
          (Class.cv (nb091AlphaDummy024 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_027`. -/
@[expose]
noncomputable def nb091AlphaDummy027 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy021 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_028`. -/
@[expose]
noncomputable def nb091AlphaDummy028 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy024 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_029`. -/
@[expose]
noncomputable def nb091AlphaDummy029 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy020 D R)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy021 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_030`. -/
@[expose]
noncomputable def nb091AlphaDummy030 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy023 D R p)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy024 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_031`. -/
@[expose]
noncomputable def nb091AlphaDummy031 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy020 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_032`. -/
@[expose]
noncomputable def nb091AlphaDummy032 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy023 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_033`. -/
@[expose]
noncomputable def nb091AlphaDummy033 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy021 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy021 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_034`. -/
@[expose]
noncomputable def nb091AlphaDummy034 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy024 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy024 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_035`. -/
@[expose]
noncomputable def nb091AlphaDummy035 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy005 D R)
          (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy005 D R)
          (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_036`. -/
@[expose]
noncomputable def nb091AlphaDummy036 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy007 D R p)
          (synWrex (nb091AlphaDummy008 D R p) (Class.cv (nb091AlphaDummy002 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy007 D R p)
          (synWrex (nb091AlphaDummy008 D R p) (Class.cv (nb091AlphaDummy002 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_037`. -/
@[expose]
noncomputable def nb091AlphaDummy037 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy006 D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_038`. -/
@[expose]
noncomputable def nb091AlphaDummy038 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy008 D R p))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_039`. -/
@[expose]
noncomputable def nb091AlphaDummy039 (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy006 D R)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy006 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_040`. -/
@[expose]
noncomputable def nb091AlphaDummy040 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy008 D R p)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy008 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_041`. -/
@[expose]
noncomputable def nb091AlphaDummy041 (D : Class) (R : Class) : Var :=
  (freshVar (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
            (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_042`. -/
@[expose]
noncomputable def nb091AlphaDummy042 (D : Class) (R : Class) : Var :=
  (freshVar (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
            (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_043`. -/
@[expose]
noncomputable def nb091AlphaDummy043 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synChwniso D)).fv ∪
      ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_044`. -/
@[expose]
noncomputable def nb091AlphaDummy044 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synChwniso D)).fv ∪
      ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_045`. -/
@[expose]
noncomputable def nb091AlphaDummy045 (D : Class) (R : Class) : Var :=
  (freshVar (((synChnwcutcode R D
        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_046`. -/
@[expose]
noncomputable def nb091AlphaDummy046 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synChnwcutcode R D (synCuni (synCuni (Class.cv p))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_047`. -/
@[expose]
noncomputable def nb091AlphaDummy047 (D : Class) (R : Class) : Var :=
  (freshVar (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
      ((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_048`. -/
@[expose]
noncomputable def nb091AlphaDummy048 (D : Class) (R : Class) : Var :=
  (freshVar (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
      ((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_049`. -/
@[expose]
noncomputable def nb091AlphaDummy049 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_050`. -/
@[expose]
noncomputable def nb091AlphaDummy050 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p))))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_051`. -/
@[expose]
noncomputable def nb091AlphaDummy051 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy047 D R)
            (synWrex (nb091AlphaDummy048 D R) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCphi (Class.cv (nb091AlphaDummy048 D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_052`. -/
@[expose]
noncomputable def nb091AlphaDummy052 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy049 D R p)
            (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_053`. -/
@[expose]
noncomputable def nb091AlphaDummy053 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
            (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
            (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
              (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv ∪
      ((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
              (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
            (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
              (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_054`. -/
@[expose]
noncomputable def nb091AlphaDummy054 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
            (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))
            (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
              (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv ∪
      ((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
            (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))
            (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
              (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_055`. -/
@[expose]
noncomputable def nb091AlphaDummy055 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
      ((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_056`. -/
@[expose]
noncomputable def nb091AlphaDummy056 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCnin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_057`. -/
@[expose]
noncomputable def nb091AlphaDummy057 (D : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_058`. -/
@[expose]
noncomputable def nb091AlphaDummy058 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_059`. -/
@[expose]
noncomputable def nb091AlphaDummy059 (D : Class) (R : Class) : Var :=
  (freshVar (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
      ((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_060`. -/
@[expose]
noncomputable def nb091AlphaDummy060 (D : Class) (R : Class) : Var :=
  (freshVar (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
      ((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_061`. -/
@[expose]
noncomputable def nb091AlphaDummy061 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_062`. -/
@[expose]
noncomputable def nb091AlphaDummy062 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p))))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_063`. -/
@[expose]
noncomputable def nb091AlphaDummy063 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb091AlphaDummy059 D R)} : Finset Var) ∪
        ({(nb091AlphaDummy060 D R)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
          (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_064`. -/
@[expose]
noncomputable def nb091AlphaDummy064 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (({(nb091AlphaDummy061 D R p)} : Finset Var) ∪
        ({(nb091AlphaDummy062 D R p)} : Finset Var) ∪ ((synWa
          (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))))
          (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_065`. -/
@[expose]
noncomputable def nb091AlphaDummy065 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy060 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_066`. -/
@[expose]
noncomputable def nb091AlphaDummy066 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy060 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_067`. -/
@[expose]
noncomputable def nb091AlphaDummy067 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy062 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_068`. -/
@[expose]
noncomputable def nb091AlphaDummy068 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy062 D R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_069`. -/
@[expose]
noncomputable def nb091AlphaDummy069 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCphi (Class.cv (nb091AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_070`. -/
@[expose]
noncomputable def nb091AlphaDummy070 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy067 D R p)
            (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy061 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCphi (Class.cv (nb091AlphaDummy068 D R p)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy062 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_071`. -/
@[expose]
noncomputable def nb091AlphaDummy071 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy065 D R)
          (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
              (synCphi (Class.cv (nb091AlphaDummy066 D R))))))).fv ∪
      ((Class.cab (nb091AlphaDummy065 D R)
          (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
              (synCphi (Class.cv (nb091AlphaDummy066 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_072`. -/
@[expose]
noncomputable def nb091AlphaDummy072 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy067 D R p)
          (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy061 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
              (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))).fv ∪
      ((Class.cab (nb091AlphaDummy067 D R p)
          (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy061 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
              (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_073`. -/
@[expose]
noncomputable def nb091AlphaDummy073 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy066 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_074`. -/
@[expose]
noncomputable def nb091AlphaDummy074 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy066 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_075`. -/
@[expose]
noncomputable def nb091AlphaDummy075 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy068 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_076`. -/
@[expose]
noncomputable def nb091AlphaDummy076 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy068 D R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_077`. -/
@[expose]
noncomputable def nb091AlphaDummy077 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy073 D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy073 D R)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy073 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_078`. -/
@[expose]
noncomputable def nb091AlphaDummy078 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy075 D R p)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy075 D R p)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy075 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_079`. -/
@[expose]
noncomputable def nb091AlphaDummy079 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_080`. -/
@[expose]
noncomputable def nb091AlphaDummy080 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_081`. -/
@[expose]
noncomputable def nb091AlphaDummy081 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_082`. -/
@[expose]
noncomputable def nb091AlphaDummy082 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_083`. -/
@[expose]
noncomputable def nb091AlphaDummy083 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_084`. -/
@[expose]
noncomputable def nb091AlphaDummy084 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_085`. -/
@[expose]
noncomputable def nb091AlphaDummy085 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy080 D R))
          (Class.cv (nb091AlphaDummy081 D R)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy080 D R))
          (Class.cv (nb091AlphaDummy081 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_086`. -/
@[expose]
noncomputable def nb091AlphaDummy086 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy083 D R p))
          (Class.cv (nb091AlphaDummy084 D R p)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy083 D R p))
          (Class.cv (nb091AlphaDummy084 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_087`. -/
@[expose]
noncomputable def nb091AlphaDummy087 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy081 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_088`. -/
@[expose]
noncomputable def nb091AlphaDummy088 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy084 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_089`. -/
@[expose]
noncomputable def nb091AlphaDummy089 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy080 D R)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy081 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_090`. -/
@[expose]
noncomputable def nb091AlphaDummy090 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy083 D R p)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy084 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_091`. -/
@[expose]
noncomputable def nb091AlphaDummy091 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy080 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_092`. -/
@[expose]
noncomputable def nb091AlphaDummy092 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy083 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_093`. -/
@[expose]
noncomputable def nb091AlphaDummy093 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy081 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy081 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_094`. -/
@[expose]
noncomputable def nb091AlphaDummy094 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy084 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy084 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_095`. -/
@[expose]
noncomputable def nb091AlphaDummy095 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy065 D R)
          (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy065 D R)
          (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_096`. -/
@[expose]
noncomputable def nb091AlphaDummy096 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy067 D R p)
          (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy062 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy067 D R p)
          (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy062 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_097`. -/
@[expose]
noncomputable def nb091AlphaDummy097 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy066 D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_098`. -/
@[expose]
noncomputable def nb091AlphaDummy098 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy068 D R p))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_099`. -/
@[expose]
noncomputable def nb091AlphaDummy099 (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy066 D R)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy066 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_100`. -/
@[expose]
noncomputable def nb091AlphaDummy100 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy068 D R p)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy068 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_101`. -/
@[expose]
noncomputable def nb091AlphaDummy101 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
      ((synCnin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_102`. -/
@[expose]
noncomputable def nb091AlphaDummy102 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCnin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_103`. -/
@[expose]
noncomputable def nb091AlphaDummy103 (D : Class) (R : Class) : Var :=
  (freshVar ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_104`. -/
@[expose]
noncomputable def nb091AlphaDummy104 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_105`. -/
@[expose]
noncomputable def nb091AlphaDummy105 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_106`. -/
@[expose]
noncomputable def nb091AlphaDummy106 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_107`. -/
@[expose]
noncomputable def nb091AlphaDummy107 (R : Class) (p : Var) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (synCuni (synCuni (Class.cv p))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_108`. -/
@[expose]
noncomputable def nb091AlphaDummy108 (R : Class) (p : Var) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (synCuni (synCuni (Class.cv p))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_109`. -/
@[expose]
noncomputable def nb091AlphaDummy109 (D : Class) (R : Class) : Var :=
  (freshVar (((synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_110`. -/
@[expose]
noncomputable def nb091AlphaDummy110 (p : Var) : Var :=
  (freshVar (((synCuni (synCuni (Class.cv p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_111`. -/
@[expose]
noncomputable def nb091AlphaDummy111 (D : Class) (R : Class) : Var :=
  (freshVar (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_112`. -/
@[expose]
noncomputable def nb091AlphaDummy112 (D : Class) (R : Class) : Var :=
  (freshVar (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_113`. -/
@[expose]
noncomputable def nb091AlphaDummy113 (p : Var) : Var :=
  (freshVar (((synCuni (Class.cv p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_114`. -/
@[expose]
noncomputable def nb091AlphaDummy114 (p : Var) : Var :=
  (freshVar (((synCuni (Class.cv p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_115`. -/
@[expose]
noncomputable def nb091AlphaDummy115 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy000 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_116`. -/
@[expose]
noncomputable def nb091AlphaDummy116 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy000 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_117`. -/
@[expose]
noncomputable def nb091AlphaDummy117 (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_118`. -/
@[expose]
noncomputable def nb091AlphaDummy118 (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_119`. -/
@[expose]
noncomputable def nb091AlphaDummy119 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy105 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_120`. -/
@[expose]
noncomputable def nb091AlphaDummy120 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy105 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_121`. -/
@[expose]
noncomputable def nb091AlphaDummy121 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
      ((Class.cv (nb091AlphaDummy107 R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_122`. -/
@[expose]
noncomputable def nb091AlphaDummy122 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
      ((Class.cv (nb091AlphaDummy107 R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_123`. -/
@[expose]
noncomputable def nb091AlphaDummy123 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCphi (Class.cv (nb091AlphaDummy120 D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_124`. -/
@[expose]
noncomputable def nb091AlphaDummy124 (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCphi (Class.cv (nb091AlphaDummy122 R p)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_125`. -/
@[expose]
noncomputable def nb091AlphaDummy125 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy119 D R)
          (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
              (synCphi (Class.cv (nb091AlphaDummy120 D R))))))).fv ∪
      ((Class.cab (nb091AlphaDummy119 D R)
          (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
              (synCphi (Class.cv (nb091AlphaDummy120 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_126`. -/
@[expose]
noncomputable def nb091AlphaDummy126 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy121 R p)
          (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
              (synCphi (Class.cv (nb091AlphaDummy122 R p))))))).fv ∪
      ((Class.cab (nb091AlphaDummy121 R p)
          (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
              (synCphi (Class.cv (nb091AlphaDummy122 R p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_127`. -/
@[expose]
noncomputable def nb091AlphaDummy127 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy120 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_128`. -/
@[expose]
noncomputable def nb091AlphaDummy128 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy120 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_129`. -/
@[expose]
noncomputable def nb091AlphaDummy129 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy122 R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_130`. -/
@[expose]
noncomputable def nb091AlphaDummy130 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy122 R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_131`. -/
@[expose]
noncomputable def nb091AlphaDummy131 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy127 D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy127 D R)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy127 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_132`. -/
@[expose]
noncomputable def nb091AlphaDummy132 (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy129 R p)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy129 R p)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy129 R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_133`. -/
@[expose]
noncomputable def nb091AlphaDummy133 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_134`. -/
@[expose]
noncomputable def nb091AlphaDummy134 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_135`. -/
@[expose]
noncomputable def nb091AlphaDummy135 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_136`. -/
@[expose]
noncomputable def nb091AlphaDummy136 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_137`. -/
@[expose]
noncomputable def nb091AlphaDummy137 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_138`. -/
@[expose]
noncomputable def nb091AlphaDummy138 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_139`. -/
@[expose]
noncomputable def nb091AlphaDummy139 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy134 D R))
          (Class.cv (nb091AlphaDummy135 D R)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy134 D R))
          (Class.cv (nb091AlphaDummy135 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_140`. -/
@[expose]
noncomputable def nb091AlphaDummy140 (R : Class) (p : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy137 R p))
          (Class.cv (nb091AlphaDummy138 R p)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy137 R p))
          (Class.cv (nb091AlphaDummy138 R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_141`. -/
@[expose]
noncomputable def nb091AlphaDummy141 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy135 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_142`. -/
@[expose]
noncomputable def nb091AlphaDummy142 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
      ((Class.cv (nb091AlphaDummy138 R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_143`. -/
@[expose]
noncomputable def nb091AlphaDummy143 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy134 D R)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy135 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_144`. -/
@[expose]
noncomputable def nb091AlphaDummy144 (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy137 R p)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy138 R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_145`. -/
@[expose]
noncomputable def nb091AlphaDummy145 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy134 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_146`. -/
@[expose]
noncomputable def nb091AlphaDummy146 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
      ((Class.cv (nb091AlphaDummy137 R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_147`. -/
@[expose]
noncomputable def nb091AlphaDummy147 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy135 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy135 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_148`. -/
@[expose]
noncomputable def nb091AlphaDummy148 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy138 R p))).fv ∪
      ((Class.cv (nb091AlphaDummy138 R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_149`. -/
@[expose]
noncomputable def nb091AlphaDummy149 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy119 D R)
          (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy119 D R)
          (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                (synCsn (synC0c))))))).fv) 0)

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

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_150`. -/
@[expose]
noncomputable def nb091AlphaDummy150 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy121 R p)
          (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy121 R p)
          (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_151`. -/
@[expose]
noncomputable def nb091AlphaDummy151 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy120 D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_152`. -/
@[expose]
noncomputable def nb091AlphaDummy152 (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy122 R p))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_153`. -/
@[expose]
noncomputable def nb091AlphaDummy153 (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy120 D R)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy120 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_154`. -/
@[expose]
noncomputable def nb091AlphaDummy154 (R : Class) (p : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy122 R p)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy122 R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_155`. -/
@[expose]
noncomputable def nb091AlphaDummy155 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy048 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_156`. -/
@[expose]
noncomputable def nb091AlphaDummy156 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy048 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_157`. -/
@[expose]
noncomputable def nb091AlphaDummy157 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy050 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_158`. -/
@[expose]
noncomputable def nb091AlphaDummy158 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy050 D R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_159`. -/
@[expose]
noncomputable def nb091AlphaDummy159 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy155 D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy155 D R)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy155 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_160`. -/
@[expose]
noncomputable def nb091AlphaDummy160 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy157 D R p)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy157 D R p)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy157 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_161`. -/
@[expose]
noncomputable def nb091AlphaDummy161 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_162`. -/
@[expose]
noncomputable def nb091AlphaDummy162 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_163`. -/
@[expose]
noncomputable def nb091AlphaDummy163 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_164`. -/
@[expose]
noncomputable def nb091AlphaDummy164 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_165`. -/
@[expose]
noncomputable def nb091AlphaDummy165 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_166`. -/
@[expose]
noncomputable def nb091AlphaDummy166 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_167`. -/
@[expose]
noncomputable def nb091AlphaDummy167 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy162 D R))
          (Class.cv (nb091AlphaDummy163 D R)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy162 D R))
          (Class.cv (nb091AlphaDummy163 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_168`. -/
@[expose]
noncomputable def nb091AlphaDummy168 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy165 D R p))
          (Class.cv (nb091AlphaDummy166 D R p)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy165 D R p))
          (Class.cv (nb091AlphaDummy166 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_169`. -/
@[expose]
noncomputable def nb091AlphaDummy169 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy163 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_170`. -/
@[expose]
noncomputable def nb091AlphaDummy170 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy166 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_171`. -/
@[expose]
noncomputable def nb091AlphaDummy171 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy162 D R)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy163 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_172`. -/
@[expose]
noncomputable def nb091AlphaDummy172 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy165 D R p)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy166 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_173`. -/
@[expose]
noncomputable def nb091AlphaDummy173 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy162 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_174`. -/
@[expose]
noncomputable def nb091AlphaDummy174 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy165 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_175`. -/
@[expose]
noncomputable def nb091AlphaDummy175 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy163 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy163 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_176`. -/
@[expose]
noncomputable def nb091AlphaDummy176 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy166 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy166 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_177`. -/
@[expose]
noncomputable def nb091AlphaDummy177 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy047 D R)
          (synWrex (nb091AlphaDummy048 D R) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_178`. -/
@[expose]
noncomputable def nb091AlphaDummy178 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))
            (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy049 D R p)
          (synWrex (nb091AlphaDummy050 D R p) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))
            (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_179`. -/
@[expose]
noncomputable def nb091AlphaDummy179 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy048 D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_180`. -/
@[expose]
noncomputable def nb091AlphaDummy180 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy050 D R p))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_181`. -/
@[expose]
noncomputable def nb091AlphaDummy181 (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_182`. -/
@[expose]
noncomputable def nb091AlphaDummy182 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy050 D R p)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy050 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_183`. -/
@[expose]
noncomputable def nb091AlphaDummy183 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy041 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_184`. -/
@[expose]
noncomputable def nb091AlphaDummy184 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy041 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_185`. -/
@[expose]
noncomputable def nb091AlphaDummy185 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy043 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_186`. -/
@[expose]
noncomputable def nb091AlphaDummy186 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy043 D R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_187`. -/
@[expose]
noncomputable def nb091AlphaDummy187 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCphi (Class.cv (nb091AlphaDummy184 D R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_188`. -/
@[expose]
noncomputable def nb091AlphaDummy188 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb091AlphaDummy185 D R p)
            (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy044 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCphi (Class.cv (nb091AlphaDummy186 D R p)))))))).fv ∪ ((synCcompl
          (Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy043 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_189`. -/
@[expose]
noncomputable def nb091AlphaDummy189 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy183 D R)
          (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
              (synCphi (Class.cv (nb091AlphaDummy184 D R))))))).fv ∪
      ((Class.cab (nb091AlphaDummy183 D R)
          (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
              (synCphi (Class.cv (nb091AlphaDummy184 D R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_190`. -/
@[expose]
noncomputable def nb091AlphaDummy190 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy185 D R p)
          (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy044 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
              (synCphi (Class.cv (nb091AlphaDummy186 D R p))))))).fv ∪
      ((Class.cab (nb091AlphaDummy185 D R p)
          (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy044 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
              (synCphi (Class.cv (nb091AlphaDummy186 D R p))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_191`. -/
@[expose]
noncomputable def nb091AlphaDummy191 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy184 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_192`. -/
@[expose]
noncomputable def nb091AlphaDummy192 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy184 D R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_193`. -/
@[expose]
noncomputable def nb091AlphaDummy193 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy186 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_194`. -/
@[expose]
noncomputable def nb091AlphaDummy194 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy186 D R p))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_195`. -/
@[expose]
noncomputable def nb091AlphaDummy195 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy191 D R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy191 D R)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy191 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_196`. -/
@[expose]
noncomputable def nb091AlphaDummy196 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091AlphaDummy193 D R p)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb091AlphaDummy193 D R p)) (synC1c))).fv ∪
      ((Class.cv (nb091AlphaDummy193 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_197`. -/
@[expose]
noncomputable def nb091AlphaDummy197 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_198`. -/
@[expose]
noncomputable def nb091AlphaDummy198 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_199`. -/
@[expose]
noncomputable def nb091AlphaDummy199 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_200`. -/
@[expose]
noncomputable def nb091AlphaDummy200 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_201`. -/
@[expose]
noncomputable def nb091AlphaDummy201 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_202`. -/
@[expose]
noncomputable def nb091AlphaDummy202 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_203`. -/
@[expose]
noncomputable def nb091AlphaDummy203 (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy198 D R))
          (Class.cv (nb091AlphaDummy199 D R)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy198 D R))
          (Class.cv (nb091AlphaDummy199 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_204`. -/
@[expose]
noncomputable def nb091AlphaDummy204 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb091AlphaDummy201 D R p))
          (Class.cv (nb091AlphaDummy202 D R p)))).fv ∪
      ((synCnin (Class.cv (nb091AlphaDummy201 D R p))
          (Class.cv (nb091AlphaDummy202 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_205`. -/
@[expose]
noncomputable def nb091AlphaDummy205 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy199 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_206`. -/
@[expose]
noncomputable def nb091AlphaDummy206 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy202 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_207`. -/
@[expose]
noncomputable def nb091AlphaDummy207 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy198 D R)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy199 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_208`. -/
@[expose]
noncomputable def nb091AlphaDummy208 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb091AlphaDummy201 D R p)))).fv ∪
      ((synCcompl (Class.cv (nb091AlphaDummy202 D R p)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_209`. -/
@[expose]
noncomputable def nb091AlphaDummy209 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy198 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_210`. -/
@[expose]
noncomputable def nb091AlphaDummy210 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy201 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_211`. -/
@[expose]
noncomputable def nb091AlphaDummy211 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy199 D R))).fv ∪
      ((Class.cv (nb091AlphaDummy199 D R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_212`. -/
@[expose]
noncomputable def nb091AlphaDummy212 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091AlphaDummy202 D R p))).fv ∪
      ((Class.cv (nb091AlphaDummy202 D R p))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_213`. -/
@[expose]
noncomputable def nb091AlphaDummy213 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy183 D R)
          (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy183 D R)
          (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
            (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
              (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_214`. -/
@[expose]
noncomputable def nb091AlphaDummy214 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091AlphaDummy185 D R p)
          (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy043 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy185 D R p)
          (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy043 D R p))
            (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
              (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_215`. -/
@[expose]
noncomputable def nb091AlphaDummy215 (D : Class) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy184 D R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_216`. -/
@[expose]
noncomputable def nb091AlphaDummy216 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb091AlphaDummy186 D R p))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_217`. -/
@[expose]
noncomputable def nb091AlphaDummy217 (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy184 D R)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy184 D R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb091_alpha_dummy_218`. -/
@[expose]
noncomputable def nb091AlphaDummy218 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb091AlphaDummy186 D R p)))).fv ∪
      ((synCphi (Class.cv (nb091AlphaDummy186 D R p)))).fv) 0)

theorem nb091_fresh_000 (D : Class) (R : Class) :
    (nb091AlphaDummy011 D R) ∉
      (((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCphi (Class.cv (nb091AlphaDummy006 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCphi (Class.cv (nb091AlphaDummy006 D R))))))).fv) :=
  by
  simpa only [nb091AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCphi (Class.cv (nb091AlphaDummy006 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCphi (Class.cv (nb091AlphaDummy006 D R))))))).fv)
      0

theorem nb091_fresh_001 (D : Class) (R : Class) :
    (nb091AlphaDummy035 D R) ∉
      (((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_002 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy036 D R p) ∉
      (((Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
              (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
              (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_003 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy012 D R p) ∉
      (((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCphi (Class.cv (nb091AlphaDummy008 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCphi (Class.cv (nb091AlphaDummy008 D R p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCphi (Class.cv (nb091AlphaDummy008 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCphi (Class.cv (nb091AlphaDummy008 D R p))))))).fv)
      0

theorem nb091_fresh_004 (D : Class) (R : Class) :
    (nb091AlphaDummy177 D R) ∉
      (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy047 D R)
            (synWrex (nb091AlphaDummy048 D R) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy177] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy047 D R)
            (synWrex (nb091AlphaDummy048 D R) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_005 (D : Class) (R : Class) :
    (nb091AlphaDummy053 D R) ∉
      (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
                (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
                (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv) :=
  by
  simpa only [nb091AlphaDummy053] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
                (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
                (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv)
      0

theorem nb091_fresh_006 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy178 D R p) ∉
      (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy049 D R p)
            (synWrex (nb091AlphaDummy050 D R p) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy178] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy049 D R p)
            (synWrex (nb091AlphaDummy050 D R p) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_007 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy054 D R p) ∉
      (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy054] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv)
      0

theorem nb091_fresh_008 (D : Class) (R : Class) :
    (nb091AlphaDummy071 D R) ∉
      (((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCphi (Class.cv (nb091AlphaDummy066 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCphi (Class.cv (nb091AlphaDummy066 D R))))))).fv) :=
  by
  simpa only [nb091AlphaDummy071] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCphi (Class.cv (nb091AlphaDummy066 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCphi (Class.cv (nb091AlphaDummy066 D R))))))).fv)
      0

theorem nb091_fresh_009 (D : Class) (R : Class) :
    (nb091AlphaDummy095 D R) ∉
      (((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy095] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_010 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy072 D R p) ∉
      (((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy061 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy061 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy072] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy061 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy061 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))).fv)
      0

theorem nb091_fresh_011 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy096 D R p) ∉
      (((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy062 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy067 D R p)
            (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy062 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy096] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy062 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy067 D R p)
            (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy062 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_012 (D : Class) (R : Class) :
    (nb091AlphaDummy149 D R) ∉
      (((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy149] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_013 (D : Class) (R : Class) :
    (nb091AlphaDummy125 D R) ∉
      (((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCphi (Class.cv (nb091AlphaDummy120 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCphi (Class.cv (nb091AlphaDummy120 D R))))))).fv) :=
  by
  simpa only [nb091AlphaDummy125] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCphi (Class.cv (nb091AlphaDummy120 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCphi (Class.cv (nb091AlphaDummy120 D R))))))).fv)
      0

theorem nb091_fresh_014 (R : Class) (p : Var) :
    (nb091AlphaDummy150 R p) ∉
      (((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy150] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_015 (R : Class) (p : Var) :
    (nb091AlphaDummy126 R p) ∉
      (((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCphi (Class.cv (nb091AlphaDummy122 R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCphi (Class.cv (nb091AlphaDummy122 R p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy126] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCphi (Class.cv (nb091AlphaDummy122 R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCphi (Class.cv (nb091AlphaDummy122 R p))))))).fv)
      0

theorem nb091_fresh_016 (D : Class) (R : Class) :
    (nb091AlphaDummy213 D R) ∉
      (((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy213] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_017 (D : Class) (R : Class) :
    (nb091AlphaDummy189 D R) ∉
      (((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCphi (Class.cv (nb091AlphaDummy184 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCphi (Class.cv (nb091AlphaDummy184 D R))))))).fv) :=
  by
  simpa only [nb091AlphaDummy189] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCphi (Class.cv (nb091AlphaDummy184 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCphi (Class.cv (nb091AlphaDummy184 D R))))))).fv)
      0

theorem nb091_fresh_018 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy214 D R p) ∉
      (((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy043 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy185 D R p)
            (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy043 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb091AlphaDummy214] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy043 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy185 D R p)
            (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy043 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb091_fresh_019 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy190 D R p) ∉
      (((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy044 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCphi (Class.cv (nb091AlphaDummy186 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy044 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCphi (Class.cv (nb091AlphaDummy186 D R p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy190] using
    freshVar_not_mem
      (((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy044 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCphi (Class.cv (nb091AlphaDummy186 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy044 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCphi (Class.cv (nb091AlphaDummy186 D R p))))))).fv)
      0

theorem nb091_fresh_020 (D : Class) (R : Class) :
    (nb091AlphaDummy115 D R) ∉ (((Class.cv (nb091AlphaDummy000 D R))).fv) := by
  simpa only [nb091AlphaDummy115] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy000 D R))).fv) 0

theorem nb091_fresh_021 (D : Class) (R : Class) :
    (nb091AlphaDummy116 D R) ∉ (((Class.cv (nb091AlphaDummy000 D R))).fv) := by
  simpa only [nb091AlphaDummy116] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy000 D R))).fv) 1

theorem nb091_distinct_022 (D : Class) (R : Class) :
    (nb091AlphaDummy115 D R) ≠ (nb091AlphaDummy116 D R) := by
  simpa only [nb091AlphaDummy115, nb091AlphaDummy116] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy000 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_023 (D : Class) (R : Class) :
    (nb091AlphaDummy005 D R) ∉
      (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy001 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy001 D R))).fv)
      0

theorem nb091_fresh_024 (D : Class) (R : Class) :
    (nb091AlphaDummy006 D R) ∉
      (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy001 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy001 D R))).fv)
      1

theorem nb091_distinct_025 (D : Class) (R : Class) :
    (nb091AlphaDummy005 D R) ≠ (nb091AlphaDummy006 D R) := by
  simpa only [nb091AlphaDummy005, nb091AlphaDummy006] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy001 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_026 (D : Class) (R : Class) :
    (nb091AlphaDummy013 D R) ∉ (((Class.cv (nb091AlphaDummy006 D R))).fv) := by
  simpa only [nb091AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy006 D R))).fv) 0

theorem nb091_fresh_027 (D : Class) (R : Class) :
    (nb091AlphaDummy014 D R) ∉ (((Class.cv (nb091AlphaDummy006 D R))).fv) := by
  simpa only [nb091AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy006 D R))).fv) 1

theorem nb091_distinct_028 (D : Class) (R : Class) :
    (nb091AlphaDummy013 D R) ≠ (nb091AlphaDummy014 D R) := by
  simpa only [nb091AlphaDummy013, nb091AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy006 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_029 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy015 D R p) ∉ (((Class.cv (nb091AlphaDummy008 D R p))).fv) := by
  simpa only [nb091AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy008 D R p))).fv) 0

theorem nb091_fresh_030 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy016 D R p) ∉ (((Class.cv (nb091AlphaDummy008 D R p))).fv) := by
  simpa only [nb091AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy008 D R p))).fv) 1

theorem nb091_distinct_031 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy016 D R p) := by
  simpa only [nb091AlphaDummy015, nb091AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy008 D R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_032 (D : Class) (R : Class) :
    (nb091AlphaDummy019 D R) ∉
      (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_033 (D : Class) (R : Class) :
    (nb091AlphaDummy020 D R) ∉
      (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_034 (D : Class) (R : Class) :
    (nb091AlphaDummy021 D R) ∉
      (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_035 (D : Class) (R : Class) :
    (nb091AlphaDummy019 D R) ≠ (nb091AlphaDummy020 D R) := by
  simpa only [nb091AlphaDummy019, nb091AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_036 (D : Class) (R : Class) :
    (nb091AlphaDummy019 D R) ≠ (nb091AlphaDummy021 D R) := by
  simpa only [nb091AlphaDummy019, nb091AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_037 (D : Class) (R : Class) :
    (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy021 D R) := by
  simpa only [nb091AlphaDummy020, nb091AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_038 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy022 D R p) ∉
      (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_039 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy023 D R p) ∉
      (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_040 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy024 D R p) ∉
      (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_041 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy022 D R p) ≠ (nb091AlphaDummy023 D R p) := by
  simpa only [nb091AlphaDummy022, nb091AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_042 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy022 D R p) ≠ (nb091AlphaDummy024 D R p) := by
  simpa only [nb091AlphaDummy022, nb091AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_043 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy024 D R p) := by
  simpa only [nb091AlphaDummy023, nb091AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_044 (D : Class) (R : Class) :
    (nb091AlphaDummy031 D R) ∉
      (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy020 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy020 D R))).fv)
      0

theorem nb091_fresh_045 (D : Class) (R : Class) :
    (nb091AlphaDummy027 D R) ∉
      (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy021 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy021 D R))).fv)
      0

theorem nb091_fresh_046 (D : Class) (R : Class) :
    (nb091AlphaDummy033 D R) ∉
      (((Class.cv (nb091AlphaDummy021 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy021 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy021 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy021 D R))).fv)
      0

theorem nb091_fresh_047 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy032 D R p) ∉
      (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy023 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy023 D R p))).fv)
      0

theorem nb091_fresh_048 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy028 D R p) ∉
      (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy024 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy024 D R p))).fv)
      0

theorem nb091_fresh_049 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy034 D R p) ∉
      (((Class.cv (nb091AlphaDummy024 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy024 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy024 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy024 D R p))).fv)
      0

theorem nb091_fresh_050 (D : Class) (R : Class) :
    (nb091AlphaDummy183 D R) ∉
      (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy041 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy183] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy041 D R))).fv)
      0

theorem nb091_fresh_051 (D : Class) (R : Class) :
    (nb091AlphaDummy184 D R) ∉
      (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy041 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy184] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy041 D R))).fv)
      1

theorem nb091_distinct_052 (D : Class) (R : Class) :
    (nb091AlphaDummy183 D R) ≠ (nb091AlphaDummy184 D R) := by
  simpa only [nb091AlphaDummy183, nb091AlphaDummy184] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy041 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_053 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy185 D R p) ∉
      (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy043 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy185] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy043 D R p))).fv)
      0

theorem nb091_fresh_054 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy186 D R p) ∉
      (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy043 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy186] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy043 D R p))).fv)
      1

theorem nb091_distinct_055 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy185 D R p) ≠ (nb091AlphaDummy186 D R p) := by
  simpa only [nb091AlphaDummy185, nb091AlphaDummy186] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy043 D R p))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_056 (D : Class) (R : Class) :
    (nb091AlphaDummy155 D R) ∉ (((Class.cv (nb091AlphaDummy048 D R))).fv) := by
  simpa only [nb091AlphaDummy155] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy048 D R))).fv) 0

theorem nb091_fresh_057 (D : Class) (R : Class) :
    (nb091AlphaDummy156 D R) ∉ (((Class.cv (nb091AlphaDummy048 D R))).fv) := by
  simpa only [nb091AlphaDummy156] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy048 D R))).fv) 1

theorem nb091_distinct_058 (D : Class) (R : Class) :
    (nb091AlphaDummy155 D R) ≠ (nb091AlphaDummy156 D R) := by
  simpa only [nb091AlphaDummy155, nb091AlphaDummy156] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy048 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_059 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy157 D R p) ∉ (((Class.cv (nb091AlphaDummy050 D R p))).fv) := by
  simpa only [nb091AlphaDummy157] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy050 D R p))).fv) 0

theorem nb091_fresh_060 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy158 D R p) ∉ (((Class.cv (nb091AlphaDummy050 D R p))).fv) := by
  simpa only [nb091AlphaDummy158] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy050 D R p))).fv) 1

theorem nb091_distinct_061 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy157 D R p) ≠ (nb091AlphaDummy158 D R p) := by
  simpa only [nb091AlphaDummy157, nb091AlphaDummy158] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy050 D R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_062 (D : Class) (R : Class) :
    (nb091AlphaDummy065 D R) ∉
      (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy060 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy065] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy060 D R))).fv)
      0

theorem nb091_fresh_063 (D : Class) (R : Class) :
    (nb091AlphaDummy066 D R) ∉
      (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy060 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy066] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy060 D R))).fv)
      1

theorem nb091_distinct_064 (D : Class) (R : Class) :
    (nb091AlphaDummy065 D R) ≠ (nb091AlphaDummy066 D R) := by
  simpa only [nb091AlphaDummy065, nb091AlphaDummy066] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy060 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_065 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy067 D R p) ∉
      (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy062 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy067] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy062 D R p))).fv)
      0

theorem nb091_fresh_066 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy068 D R p) ∉
      (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy062 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy068] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy062 D R p))).fv)
      1

theorem nb091_distinct_067 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy067 D R p) ≠ (nb091AlphaDummy068 D R p) := by
  simpa only [nb091AlphaDummy067, nb091AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy062 D R p))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_068 (D : Class) (R : Class) :
    (nb091AlphaDummy073 D R) ∉ (((Class.cv (nb091AlphaDummy066 D R))).fv) := by
  simpa only [nb091AlphaDummy073] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy066 D R))).fv) 0

theorem nb091_fresh_069 (D : Class) (R : Class) :
    (nb091AlphaDummy074 D R) ∉ (((Class.cv (nb091AlphaDummy066 D R))).fv) := by
  simpa only [nb091AlphaDummy074] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy066 D R))).fv) 1

theorem nb091_distinct_070 (D : Class) (R : Class) :
    (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy074 D R) := by
  simpa only [nb091AlphaDummy073, nb091AlphaDummy074] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy066 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_071 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy075 D R p) ∉ (((Class.cv (nb091AlphaDummy068 D R p))).fv) := by
  simpa only [nb091AlphaDummy075] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy068 D R p))).fv) 0

theorem nb091_fresh_072 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy076 D R p) ∉ (((Class.cv (nb091AlphaDummy068 D R p))).fv) := by
  simpa only [nb091AlphaDummy076] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy068 D R p))).fv) 1

theorem nb091_distinct_073 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy076 D R p) := by
  simpa only [nb091AlphaDummy075, nb091AlphaDummy076] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy068 D R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_074 (D : Class) (R : Class) :
    (nb091AlphaDummy079 D R) ∉
      (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy079] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_075 (D : Class) (R : Class) :
    (nb091AlphaDummy080 D R) ∉
      (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy080] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_076 (D : Class) (R : Class) :
    (nb091AlphaDummy081 D R) ∉
      (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy081] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_077 (D : Class) (R : Class) :
    (nb091AlphaDummy079 D R) ≠ (nb091AlphaDummy080 D R) := by
  simpa only [nb091AlphaDummy079, nb091AlphaDummy080] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

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

theorem nb091_distinct_078 (D : Class) (R : Class) :
    (nb091AlphaDummy079 D R) ≠ (nb091AlphaDummy081 D R) := by
  simpa only [nb091AlphaDummy079, nb091AlphaDummy081] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_079 (D : Class) (R : Class) :
    (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy081 D R) := by
  simpa only [nb091AlphaDummy080, nb091AlphaDummy081] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_080 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy082 D R p) ∉
      (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy082] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_081 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy083 D R p) ∉
      (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy083] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_082 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy084 D R p) ∉
      (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy084] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_083 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy082 D R p) ≠ (nb091AlphaDummy083 D R p) := by
  simpa only [nb091AlphaDummy082, nb091AlphaDummy083] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_084 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy082 D R p) ≠ (nb091AlphaDummy084 D R p) := by
  simpa only [nb091AlphaDummy082, nb091AlphaDummy084] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_085 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy084 D R p) := by
  simpa only [nb091AlphaDummy083, nb091AlphaDummy084] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_086 (D : Class) (R : Class) :
    (nb091AlphaDummy091 D R) ∉
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy080 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy091] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy080 D R))).fv)
      0

theorem nb091_fresh_087 (D : Class) (R : Class) :
    (nb091AlphaDummy087 D R) ∉
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy081 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy087] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy081 D R))).fv)
      0

theorem nb091_fresh_088 (D : Class) (R : Class) :
    (nb091AlphaDummy093 D R) ∉
      (((Class.cv (nb091AlphaDummy081 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy081 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy093] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy081 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy081 D R))).fv)
      0

theorem nb091_fresh_089 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy092 D R p) ∉
      (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy083 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy092] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy083 D R p))).fv)
      0

theorem nb091_fresh_090 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy088 D R p) ∉
      (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy084 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy088] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy084 D R p))).fv)
      0

theorem nb091_fresh_091 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy094 D R p) ∉
      (((Class.cv (nb091AlphaDummy084 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy084 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy094] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy084 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy084 D R p))).fv)
      0

theorem nb091_fresh_092 (D : Class) (R : Class) :
    (nb091AlphaDummy119 D R) ∉
      (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy105 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy119] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy105 D R))).fv)
      0

theorem nb091_fresh_093 (D : Class) (R : Class) :
    (nb091AlphaDummy120 D R) ∉
      (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy105 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy120] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy105 D R))).fv)
      1

theorem nb091_distinct_094 (D : Class) (R : Class) :
    (nb091AlphaDummy119 D R) ≠ (nb091AlphaDummy120 D R) := by
  simpa only [nb091AlphaDummy119, nb091AlphaDummy120] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy105 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_095 (R : Class) (p : Var) :
    (nb091AlphaDummy121 R p) ∉
      (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy107 R p))).fv) :=
  by
  simpa only [nb091AlphaDummy121] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy107 R p))).fv)
      0

theorem nb091_fresh_096 (R : Class) (p : Var) :
    (nb091AlphaDummy122 R p) ∉
      (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy107 R p))).fv) :=
  by
  simpa only [nb091AlphaDummy122] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy107 R p))).fv)
      1

theorem nb091_distinct_097 (R : Class) (p : Var) :
    (nb091AlphaDummy121 R p) ≠ (nb091AlphaDummy122 R p) := by
  simpa only [nb091AlphaDummy121, nb091AlphaDummy122] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy107 R p))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_098 (D : Class) (R : Class) :
    (nb091AlphaDummy127 D R) ∉ (((Class.cv (nb091AlphaDummy120 D R))).fv) := by
  simpa only [nb091AlphaDummy127] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy120 D R))).fv) 0

theorem nb091_fresh_099 (D : Class) (R : Class) :
    (nb091AlphaDummy128 D R) ∉ (((Class.cv (nb091AlphaDummy120 D R))).fv) := by
  simpa only [nb091AlphaDummy128] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy120 D R))).fv) 1

theorem nb091_distinct_100 (D : Class) (R : Class) :
    (nb091AlphaDummy127 D R) ≠ (nb091AlphaDummy128 D R) := by
  simpa only [nb091AlphaDummy127, nb091AlphaDummy128] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy120 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_101 (R : Class) (p : Var) :
    (nb091AlphaDummy129 R p) ∉ (((Class.cv (nb091AlphaDummy122 R p))).fv) := by
  simpa only [nb091AlphaDummy129] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy122 R p))).fv) 0

theorem nb091_fresh_102 (R : Class) (p : Var) :
    (nb091AlphaDummy130 R p) ∉ (((Class.cv (nb091AlphaDummy122 R p))).fv) := by
  simpa only [nb091AlphaDummy130] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy122 R p))).fv) 1

theorem nb091_distinct_103 (R : Class) (p : Var) :
    (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy130 R p) := by
  simpa only [nb091AlphaDummy129, nb091AlphaDummy130] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy122 R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_104 (D : Class) (R : Class) :
    (nb091AlphaDummy133 D R) ∉
      (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy133] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_105 (D : Class) (R : Class) :
    (nb091AlphaDummy134 D R) ∉
      (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy134] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_106 (D : Class) (R : Class) :
    (nb091AlphaDummy135 D R) ∉
      (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy135] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_107 (D : Class) (R : Class) :
    (nb091AlphaDummy133 D R) ≠ (nb091AlphaDummy134 D R) := by
  simpa only [nb091AlphaDummy133, nb091AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_108 (D : Class) (R : Class) :
    (nb091AlphaDummy133 D R) ≠ (nb091AlphaDummy135 D R) := by
  simpa only [nb091AlphaDummy133, nb091AlphaDummy135] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_109 (D : Class) (R : Class) :
    (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy135 D R) := by
  simpa only [nb091AlphaDummy134, nb091AlphaDummy135] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_110 (R : Class) (p : Var) :
    (nb091AlphaDummy136 R p) ∉
      (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy136] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_111 (R : Class) (p : Var) :
    (nb091AlphaDummy137 R p) ∉
      (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy137] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_112 (R : Class) (p : Var) :
    (nb091AlphaDummy138 R p) ∉
      (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy138] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_113 (R : Class) (p : Var) :
    (nb091AlphaDummy136 R p) ≠ (nb091AlphaDummy137 R p) := by
  simpa only [nb091AlphaDummy136, nb091AlphaDummy137] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_114 (R : Class) (p : Var) :
    (nb091AlphaDummy136 R p) ≠ (nb091AlphaDummy138 R p) := by
  simpa only [nb091AlphaDummy136, nb091AlphaDummy138] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_115 (R : Class) (p : Var) :
    (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy138 R p) := by
  simpa only [nb091AlphaDummy137, nb091AlphaDummy138] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_116 (D : Class) (R : Class) :
    (nb091AlphaDummy145 D R) ∉
      (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy134 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy145] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy134 D R))).fv)
      0

theorem nb091_fresh_117 (D : Class) (R : Class) :
    (nb091AlphaDummy141 D R) ∉
      (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy135 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy141] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy135 D R))).fv)
      0

theorem nb091_fresh_118 (D : Class) (R : Class) :
    (nb091AlphaDummy147 D R) ∉
      (((Class.cv (nb091AlphaDummy135 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy135 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy147] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy135 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy135 D R))).fv)
      0

theorem nb091_fresh_119 (R : Class) (p : Var) :
    (nb091AlphaDummy146 R p) ∉
      (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy137 R p))).fv) :=
  by
  simpa only [nb091AlphaDummy146] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy137 R p))).fv)
      0

theorem nb091_fresh_120 (R : Class) (p : Var) :
    (nb091AlphaDummy142 R p) ∉
      (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy138 R p))).fv) :=
  by
  simpa only [nb091AlphaDummy142] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy138 R p))).fv)
      0

theorem nb091_fresh_121 (R : Class) (p : Var) :
    (nb091AlphaDummy148 R p) ∉
      (((Class.cv (nb091AlphaDummy138 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy138 R p))).fv) :=
  by
  simpa only [nb091AlphaDummy148] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy138 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy138 R p))).fv)
      0

theorem nb091_fresh_122 (D : Class) (R : Class) :
    (nb091AlphaDummy161 D R) ∉
      (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy161] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_123 (D : Class) (R : Class) :
    (nb091AlphaDummy162 D R) ∉
      (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy162] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_124 (D : Class) (R : Class) :
    (nb091AlphaDummy163 D R) ∉
      (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy163] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_125 (D : Class) (R : Class) :
    (nb091AlphaDummy161 D R) ≠ (nb091AlphaDummy162 D R) := by
  simpa only [nb091AlphaDummy161, nb091AlphaDummy162] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_126 (D : Class) (R : Class) :
    (nb091AlphaDummy161 D R) ≠ (nb091AlphaDummy163 D R) := by
  simpa only [nb091AlphaDummy161, nb091AlphaDummy163] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_127 (D : Class) (R : Class) :
    (nb091AlphaDummy162 D R) ≠ (nb091AlphaDummy163 D R) := by
  simpa only [nb091AlphaDummy162, nb091AlphaDummy163] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_128 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy164 D R p) ∉
      (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy164] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_129 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy165 D R p) ∉
      (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy165] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_130 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy166 D R p) ∉
      (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy166] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_131 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy164 D R p) ≠ (nb091AlphaDummy165 D R p) := by
  simpa only [nb091AlphaDummy164, nb091AlphaDummy165] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_132 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy164 D R p) ≠ (nb091AlphaDummy166 D R p) := by
  simpa only [nb091AlphaDummy164, nb091AlphaDummy166] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_133 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy165 D R p) ≠ (nb091AlphaDummy166 D R p) := by
  simpa only [nb091AlphaDummy165, nb091AlphaDummy166] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_134 (D : Class) (R : Class) :
    (nb091AlphaDummy173 D R) ∉
      (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy162 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy173] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy162 D R))).fv)
      0

theorem nb091_fresh_135 (D : Class) (R : Class) :
    (nb091AlphaDummy169 D R) ∉
      (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy163 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy169] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy163 D R))).fv)
      0

theorem nb091_fresh_136 (D : Class) (R : Class) :
    (nb091AlphaDummy175 D R) ∉
      (((Class.cv (nb091AlphaDummy163 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy163 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy175] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy163 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy163 D R))).fv)
      0

theorem nb091_fresh_137 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy174 D R p) ∉
      (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy165 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy174] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy165 D R p))).fv)
      0

theorem nb091_fresh_138 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy170 D R p) ∉
      (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy166 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy170] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy166 D R p))).fv)
      0

theorem nb091_fresh_139 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy176 D R p) ∉
      (((Class.cv (nb091AlphaDummy166 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy166 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy176] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy166 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy166 D R p))).fv)
      0

theorem nb091_fresh_140 (D : Class) (R : Class) :
    (nb091AlphaDummy191 D R) ∉ (((Class.cv (nb091AlphaDummy184 D R))).fv) := by
  simpa only [nb091AlphaDummy191] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy184 D R))).fv) 0

theorem nb091_fresh_141 (D : Class) (R : Class) :
    (nb091AlphaDummy192 D R) ∉ (((Class.cv (nb091AlphaDummy184 D R))).fv) := by
  simpa only [nb091AlphaDummy192] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy184 D R))).fv) 1

theorem nb091_distinct_142 (D : Class) (R : Class) :
    (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy192 D R) := by
  simpa only [nb091AlphaDummy191, nb091AlphaDummy192] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy184 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_143 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy193 D R p) ∉ (((Class.cv (nb091AlphaDummy186 D R p))).fv) := by
  simpa only [nb091AlphaDummy193] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy186 D R p))).fv) 0

theorem nb091_fresh_144 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy194 D R p) ∉ (((Class.cv (nb091AlphaDummy186 D R p))).fv) := by
  simpa only [nb091AlphaDummy194] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy186 D R p))).fv) 1

theorem nb091_distinct_145 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy194 D R p) := by
  simpa only [nb091AlphaDummy193, nb091AlphaDummy194] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy186 D R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_146 (D : Class) (R : Class) :
    (nb091AlphaDummy197 D R) ∉
      (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy197] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_147 (D : Class) (R : Class) :
    (nb091AlphaDummy198 D R) ∉
      (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy198] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_148 (D : Class) (R : Class) :
    (nb091AlphaDummy199 D R) ∉
      (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy199] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_149 (D : Class) (R : Class) :
    (nb091AlphaDummy197 D R) ≠ (nb091AlphaDummy198 D R) := by
  simpa only [nb091AlphaDummy197, nb091AlphaDummy198] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_150 (D : Class) (R : Class) :
    (nb091AlphaDummy197 D R) ≠ (nb091AlphaDummy199 D R) := by
  simpa only [nb091AlphaDummy197, nb091AlphaDummy199] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_151 (D : Class) (R : Class) :
    (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy199 D R) := by
  simpa only [nb091AlphaDummy198, nb091AlphaDummy199] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_152 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy200 D R p) ∉
      (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy200] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) 0

theorem nb091_fresh_153 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy201 D R p) ∉
      (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy201] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) 1

theorem nb091_fresh_154 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy202 D R p) ∉
      (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb091AlphaDummy202] using
    freshVar_not_mem (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) 2

theorem nb091_distinct_155 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy200 D R p) ≠ (nb091AlphaDummy201 D R p) := by
  simpa only [nb091AlphaDummy200, nb091AlphaDummy201] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_156 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy200 D R p) ≠ (nb091AlphaDummy202 D R p) := by
  simpa only [nb091AlphaDummy200, nb091AlphaDummy202] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_157 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy202 D R p) := by
  simpa only [nb091AlphaDummy201, nb091AlphaDummy202] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_158 (D : Class) (R : Class) :
    (nb091AlphaDummy209 D R) ∉
      (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy198 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy209] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy198 D R))).fv)
      0

theorem nb091_fresh_159 (D : Class) (R : Class) :
    (nb091AlphaDummy205 D R) ∉
      (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy199 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy205] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy199 D R))).fv)
      0

theorem nb091_fresh_160 (D : Class) (R : Class) :
    (nb091AlphaDummy211 D R) ∉
      (((Class.cv (nb091AlphaDummy199 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy199 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy211] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy199 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy199 D R))).fv)
      0

theorem nb091_fresh_161 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy210 D R p) ∉
      (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy201 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy210] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy201 D R p))).fv)
      0

theorem nb091_fresh_162 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy206 D R p) ∉
      (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy202 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy206] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy202 D R p))).fv)
      0

theorem nb091_fresh_163 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy212 D R p) ∉
      (((Class.cv (nb091AlphaDummy202 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy202 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy212] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy202 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy202 D R p))).fv)
      0

theorem nb091_fresh_164 (p : Var) : (nb091AlphaDummy117 p) ∉ (((Class.cv p)).fv) := by
  simpa only [nb091AlphaDummy117] using freshVar_not_mem (((Class.cv p)).fv) 0

theorem nb091_fresh_165 (p : Var) : (nb091AlphaDummy118 p) ∉ (((Class.cv p)).fv) := by
  simpa only [nb091AlphaDummy118] using freshVar_not_mem (((Class.cv p)).fv) 1

theorem nb091_distinct_166 (p : Var) :
    (nb091AlphaDummy117 p) ≠ (nb091AlphaDummy118 p) := by
  simpa only [nb091AlphaDummy117, nb091AlphaDummy118] using
    (freshVar_injective (((Class.cv p)).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_167 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy007 D R p) ∉
      (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy007] using
    freshVar_not_mem (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) 0

theorem nb091_fresh_168 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy008 D R p) ∉
      (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy008] using
    freshVar_not_mem (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) 1

theorem nb091_distinct_169 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy007 D R p) ≠ (nb091AlphaDummy008 D R p) := by
  simpa only [nb091AlphaDummy007, nb091AlphaDummy008] using
    (freshVar_injective
      (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb091_fresh_170 (D : Class) (R : Class) :
    (nb091AlphaDummy017 D R) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy013 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy013 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy013 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy013 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy013 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy013 D R))).fv)
      0

theorem nb091_fresh_171 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy018 D R p) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy015 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy015 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy015 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy015 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy015 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy015 D R p))).fv)
      0

theorem nb091_fresh_172 (D : Class) (R : Class) :
    (nb091AlphaDummy077 D R) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy073 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy073 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy073 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy077] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy073 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy073 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy073 D R))).fv)
      0

theorem nb091_fresh_173 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy078 D R p) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy075 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy075 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy075 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy078] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy075 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy075 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy075 D R p))).fv)
      0

theorem nb091_fresh_174 (D : Class) (R : Class) :
    (nb091AlphaDummy131 D R) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy127 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy127 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy127 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy131] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy127 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy127 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy127 D R))).fv)
      0

theorem nb091_fresh_175 (R : Class) (p : Var) :
    (nb091AlphaDummy132 R p) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy129 R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy129 R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy129 R p))).fv) :=
  by
  simpa only [nb091AlphaDummy132] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy129 R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy129 R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy129 R p))).fv)
      0

theorem nb091_fresh_176 (D : Class) (R : Class) :
    (nb091AlphaDummy159 D R) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy155 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy155 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy155 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy159] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy155 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy155 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy155 D R))).fv)
      0

theorem nb091_fresh_177 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy160 D R p) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy157 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy157 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy157 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy160] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy157 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy157 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy157 D R p))).fv)
      0

theorem nb091_fresh_178 (D : Class) (R : Class) :
    (nb091AlphaDummy195 D R) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy191 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy191 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy191 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy195] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy191 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy191 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy191 D R))).fv)
      0

theorem nb091_fresh_179 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy196 D R p) ∉
      (((Wff.classMem (Class.cv (nb091AlphaDummy193 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy193 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy193 D R p))).fv) :=
  by
  simpa only [nb091AlphaDummy196] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091AlphaDummy193 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy193 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy193 D R p))).fv)
      0

theorem nb091_fresh_180 (D : Class) (R : Class) :
    (nb091AlphaDummy105 D R) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv) :=
  by
  simpa only [nb091AlphaDummy105] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv)
      0

theorem nb091_fresh_181 (D : Class) (R : Class) :
    (nb091AlphaDummy106 D R) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv) :=
  by
  simpa only [nb091AlphaDummy106] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv)
      1

theorem nb091_distinct_182 (D : Class) (R : Class) :
    (nb091AlphaDummy105 D R) ≠ (nb091AlphaDummy106 D R) := by
  simpa only [nb091AlphaDummy105, nb091AlphaDummy106] using
    (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_183 (R : Class) (p : Var) :
    (nb091AlphaDummy107 R p) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) :=
  by
  simpa only [nb091AlphaDummy107] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv)
      0

theorem nb091_fresh_184 (R : Class) (p : Var) :
    (nb091AlphaDummy108 R p) ∉
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) :=
  by
  simpa only [nb091AlphaDummy108] using
    freshVar_not_mem
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv)
      1

theorem nb091_distinct_185 (R : Class) (p : Var) :
    (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy108 R p) := by
  simpa only [nb091AlphaDummy107, nb091AlphaDummy108] using
    (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_186 (D : Class) (R : Class) :
    (nb091AlphaDummy009 D R) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCphi (Class.cv (nb091AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCphi (Class.cv (nb091AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_187 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy010 D R p) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy007 D R p)
              (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy008 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
                (Class.cv (nb091AlphaDummy002 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy007 D R p)
              (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy008 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
                (Class.cv (nb091AlphaDummy002 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_188 (D : Class) (R : Class) :
    (nb091AlphaDummy051 D R) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                            (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCphi (Class.cv (nb091AlphaDummy048 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy051] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                            (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCphi (Class.cv (nb091AlphaDummy048 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_189 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy052 D R p) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy049 D R p)
              (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy052] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy049 D R p)
              (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_190 (D : Class) (R : Class) :
    (nb091AlphaDummy069 D R) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCphi (Class.cv (nb091AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy069] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCphi (Class.cv (nb091AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_191 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy070 D R p) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy067 D R p)
              (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy061 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy068 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
                (Class.cv (nb091AlphaDummy062 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy070] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy067 D R p)
              (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy061 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy068 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
                (Class.cv (nb091AlphaDummy062 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_192 (D : Class) (R : Class) :
    (nb091AlphaDummy123 D R) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCphi (Class.cv (nb091AlphaDummy120 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy123] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCphi (Class.cv (nb091AlphaDummy120 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_193 (R : Class) (p : Var) :
    (nb091AlphaDummy124 R p) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCphi (Class.cv (nb091AlphaDummy122 R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy124] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCphi (Class.cv (nb091AlphaDummy122 R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_194 (D : Class) (R : Class) :
    (nb091AlphaDummy187 D R) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCphi (Class.cv (nb091AlphaDummy184 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy187] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCphi (Class.cv (nb091AlphaDummy184 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_195 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy188 D R p) ∉
      (((synCcompl (Class.cab (nb091AlphaDummy185 D R p)
              (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy044 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy186 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
                (Class.cv (nb091AlphaDummy043 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy188] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb091AlphaDummy185 D R p)
              (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy044 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy186 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
                (Class.cv (nb091AlphaDummy043 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb091_fresh_196 (D : Class) (R : Class) :
    (nb091AlphaDummy029 D R) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy020 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy021 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy020 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy021 D R)))).fv)
      0

theorem nb091_fresh_197 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy030 D R p) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy023 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy024 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy023 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy024 D R p)))).fv)
      0

theorem nb091_fresh_198 (D : Class) (R : Class) :
    (nb091AlphaDummy089 D R) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy080 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy081 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy089] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy080 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy081 D R)))).fv)
      0

theorem nb091_fresh_199 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy090 D R p) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy083 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy084 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy090] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy083 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy084 D R p)))).fv)
      0

theorem nb091_fresh_200 (D : Class) (R : Class) :
    (nb091AlphaDummy143 D R) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy134 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy135 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy143] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy134 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy135 D R)))).fv)
      0

theorem nb091_fresh_201 (R : Class) (p : Var) :
    (nb091AlphaDummy144 R p) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy137 R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy138 R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy144] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy137 R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy138 R p)))).fv)
      0

theorem nb091_fresh_202 (D : Class) (R : Class) :
    (nb091AlphaDummy171 D R) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy162 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy163 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy171] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy162 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy163 D R)))).fv)
      0

theorem nb091_fresh_203 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy172 D R p) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy165 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy166 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy172] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy165 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy166 D R p)))).fv)
      0

theorem nb091_fresh_204 (D : Class) (R : Class) :
    (nb091AlphaDummy207 D R) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy198 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy199 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy207] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy198 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy199 D R)))).fv)
      0

theorem nb091_fresh_205 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy208 D R p) ∉
      (((synCcompl (Class.cv (nb091AlphaDummy201 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy202 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy208] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb091AlphaDummy201 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy202 D R p)))).fv)
      0

theorem nb091_fresh_206 (D : Class) (R : Class) :
    (nb091AlphaDummy037 D R) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy006 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy006 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_207 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy038 D R p) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy008 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy008 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_208 (D : Class) (R : Class) :
    (nb091AlphaDummy179 D R) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy048 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy179] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy048 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_209 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy180 D R p) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy050 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy180] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy050 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_210 (D : Class) (R : Class) :
    (nb091AlphaDummy097 D R) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy066 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy097] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy066 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_211 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy098 D R p) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy068 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy098] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy068 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_212 (D : Class) (R : Class) :
    (nb091AlphaDummy151 D R) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy120 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy151] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy120 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_213 (R : Class) (p : Var) :
    (nb091AlphaDummy152 R p) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy122 R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy152] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy122 R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_214 (D : Class) (R : Class) :
    (nb091AlphaDummy215 D R) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy184 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy215] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy184 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_215 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy216 D R p) ∉
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy186 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb091AlphaDummy216] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy186 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb091_fresh_216 (D : Class) (R : Class) :
    (nb091AlphaDummy045 D R) ∉
      (((synChnwcutcode R D
          (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv) :=
  by
  simpa only [nb091AlphaDummy045] using
    freshVar_not_mem
      (((synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv)
      0

theorem nb091_fresh_217 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy046 D R p) ∉
      (((synChnwcutcode R D (synCuni (synCuni (Class.cv p))))).fv) :=
  by
  simpa only [nb091AlphaDummy046] using
    freshVar_not_mem (((synChnwcutcode R D (synCuni (synCuni (Class.cv p))))).fv) 0

theorem nb091_fresh_218 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∉
      (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
              (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv) :=
  by
  simpa only [nb091AlphaDummy041] using
    freshVar_not_mem
      (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
              (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
      0

theorem nb091_fresh_219 (D : Class) (R : Class) :
    (nb091AlphaDummy042 D R) ∉
      (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
              (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv) :=
  by
  simpa only [nb091AlphaDummy042] using
    freshVar_not_mem
      (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
              (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
      1

theorem nb091_distinct_220 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy042 D R) := by
  simpa only [nb091AlphaDummy041, nb091AlphaDummy042] using
    (freshVar_injective (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
              (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_221 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∉
      (((synChwniso D)).fv ∪
        ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv) :=
  by
  simpa only [nb091AlphaDummy043] using
    freshVar_not_mem
      (((synChwniso D)).fv ∪
        ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv)
      0

theorem nb091_fresh_222 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∉
      (((synChwniso D)).fv ∪
        ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv) :=
  by
  simpa only [nb091AlphaDummy044] using
    freshVar_not_mem
      (((synChwniso D)).fv ∪
        ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv)
      1

theorem nb091_distinct_223 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy044 D R p) := by
  simpa only [nb091AlphaDummy043, nb091AlphaDummy044] using
    (freshVar_injective (((synChwniso D)).fv ∪
        ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_224 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy059] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
