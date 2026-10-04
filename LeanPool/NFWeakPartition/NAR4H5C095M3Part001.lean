/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4H5C095M3Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_000`. -/
@[expose]
noncomputable def nb095AlphaDummy000 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_001`. -/
@[expose]
noncomputable def nb095AlphaDummy001 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_002`. -/
@[expose]
noncomputable def nb095AlphaDummy002 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_003`. -/
@[expose]
noncomputable def nb095AlphaDummy003 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
          ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_004`. -/
@[expose]
noncomputable def nb095AlphaDummy004 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
          ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_005`. -/
@[expose]
noncomputable def nb095AlphaDummy005 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv u))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
      ((synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_006`. -/
@[expose]
noncomputable def nb095AlphaDummy006 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv u))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
      ((synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
    1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_007`. -/
@[expose]
noncomputable def nb095AlphaDummy007 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_008`. -/
@[expose]
noncomputable def nb095AlphaDummy008 (f : Var) : Var :=
  (freshVar (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
      ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_009`. -/
@[expose]
noncomputable def nb095AlphaDummy009 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcom (Class.cv (nb095AlphaDummy000 D R S_cls E))
          (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_010`. -/
@[expose]
noncomputable def nb095AlphaDummy010 (f : Var) : Var :=
  (freshVar (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_011`. -/
@[expose]
noncomputable def nb095AlphaDummy011 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
      ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_012`. -/
@[expose]
noncomputable def nb095AlphaDummy012 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
      ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_013`. -/
@[expose]
noncomputable def nb095AlphaDummy013 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
      ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_014`. -/
@[expose]
noncomputable def nb095AlphaDummy014 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_015`. -/
@[expose]
noncomputable def nb095AlphaDummy015 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_016`. -/
@[expose]
noncomputable def nb095AlphaDummy016 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_017`. -/
@[expose]
noncomputable def nb095AlphaDummy017 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy011 D R S_cls E)} : Finset Var) ∪
        ({(nb095AlphaDummy012 D R S_cls E)} : Finset Var) ∪
      ((synWex (nb095AlphaDummy013 D R S_cls E) (synWa
            (synWbr (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
              (Class.cv (nb095AlphaDummy013 D R S_cls E)))
            (synWbr (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Class.cv (nb095AlphaDummy000 D R S_cls E))
              (Class.cv (nb095AlphaDummy012 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_018`. -/
@[expose]
noncomputable def nb095AlphaDummy018 (f : Var) : Var :=
  (freshVar (({(nb095AlphaDummy014 f)} : Finset Var) ∪
        ({(nb095AlphaDummy015 f)} : Finset Var) ∪ ((synWex (nb095AlphaDummy016 f) (synWa
            (synWbr (Class.cv (nb095AlphaDummy014 f)) (synCcnv (Class.cv f))
              (Class.cv (nb095AlphaDummy016 f)))
            (synWbr (Class.cv (nb095AlphaDummy016 f)) (Class.cv f)
              (Class.cv (nb095AlphaDummy015 f)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_019`. -/
@[expose]
noncomputable def nb095AlphaDummy019 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_020`. -/
@[expose]
noncomputable def nb095AlphaDummy020 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_021`. -/
@[expose]
noncomputable def nb095AlphaDummy021 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy014 f))).fv ∪
      ((Class.cv (nb095AlphaDummy015 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_022`. -/
@[expose]
noncomputable def nb095AlphaDummy022 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy014 f))).fv ∪
      ((Class.cv (nb095AlphaDummy015 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_023`. -/
@[expose]
noncomputable def nb095AlphaDummy023 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_024`. -/
@[expose]
noncomputable def nb095AlphaDummy024 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCphi (Class.cv (nb095AlphaDummy022 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_025`. -/
@[expose]
noncomputable def nb095AlphaDummy025 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy019 D R S_cls E)
          (synWrex (nb095AlphaDummy020 D R S_cls E)
            (Class.cv (nb095AlphaDummy011 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy019 D R S_cls E)
          (synWrex (nb095AlphaDummy020 D R S_cls E)
            (Class.cv (nb095AlphaDummy011 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_026`. -/
@[expose]
noncomputable def nb095AlphaDummy026 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy021 f)
          (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
              (synCphi (Class.cv (nb095AlphaDummy022 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy021 f)
          (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
              (synCphi (Class.cv (nb095AlphaDummy022 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_027`. -/
@[expose]
noncomputable def nb095AlphaDummy027 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_028`. -/
@[expose]
noncomputable def nb095AlphaDummy028 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_029`. -/
@[expose]
noncomputable def nb095AlphaDummy029 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy022 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_030`. -/
@[expose]
noncomputable def nb095AlphaDummy030 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy022 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_031`. -/
@[expose]
noncomputable def nb095AlphaDummy031 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy027 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy027 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_032`. -/
@[expose]
noncomputable def nb095AlphaDummy032 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy029 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy029 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy029 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_033`. -/
@[expose]
noncomputable def nb095AlphaDummy033 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_034`. -/
@[expose]
noncomputable def nb095AlphaDummy034 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_035`. -/
@[expose]
noncomputable def nb095AlphaDummy035 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_036`. -/
@[expose]
noncomputable def nb095AlphaDummy036 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_037`. -/
@[expose]
noncomputable def nb095AlphaDummy037 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_038`. -/
@[expose]
noncomputable def nb095AlphaDummy038 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_039`. -/
@[expose]
noncomputable def nb095AlphaDummy039 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy034 D R S_cls E))
          (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy034 D R S_cls E))
          (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_040`. -/
@[expose]
noncomputable def nb095AlphaDummy040 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy037 f))
          (Class.cv (nb095AlphaDummy038 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy037 f)) (Class.cv (nb095AlphaDummy038 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_041`. -/
@[expose]
noncomputable def nb095AlphaDummy041 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_042`. -/
@[expose]
noncomputable def nb095AlphaDummy042 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy037 f))).fv ∪
      ((Class.cv (nb095AlphaDummy038 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_043`. -/
@[expose]
noncomputable def nb095AlphaDummy043 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy034 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy035 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_044`. -/
@[expose]
noncomputable def nb095AlphaDummy044 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy037 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy038 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_045`. -/
@[expose]
noncomputable def nb095AlphaDummy045 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_046`. -/
@[expose]
noncomputable def nb095AlphaDummy046 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy037 f))).fv ∪
      ((Class.cv (nb095AlphaDummy037 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_047`. -/
@[expose]
noncomputable def nb095AlphaDummy047 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_048`. -/
@[expose]
noncomputable def nb095AlphaDummy048 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy038 f))).fv ∪
      ((Class.cv (nb095AlphaDummy038 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_049`. -/
@[expose]
noncomputable def nb095AlphaDummy049 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy019 D R S_cls E)
          (synWrex (nb095AlphaDummy020 D R S_cls E)
            (Class.cv (nb095AlphaDummy012 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy019 D R S_cls E)
          (synWrex (nb095AlphaDummy020 D R S_cls E)
            (Class.cv (nb095AlphaDummy012 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_050`. -/
@[expose]
noncomputable def nb095AlphaDummy050 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy021 f)
          (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy021 f)
          (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy015 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy022 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_051`. -/
@[expose]
noncomputable def nb095AlphaDummy051 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_052`. -/
@[expose]
noncomputable def nb095AlphaDummy052 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy022 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_053`. -/
@[expose]
noncomputable def nb095AlphaDummy053 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_054`. -/
@[expose]
noncomputable def nb095AlphaDummy054 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy022 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy022 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_055`. -/
@[expose]
noncomputable def nb095AlphaDummy055 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_056`. -/
@[expose]
noncomputable def nb095AlphaDummy056 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_057`. -/
@[expose]
noncomputable def nb095AlphaDummy057 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy014 f))).fv ∪
      ((Class.cv (nb095AlphaDummy016 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_058`. -/
@[expose]
noncomputable def nb095AlphaDummy058 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy014 f))).fv ∪
      ((Class.cv (nb095AlphaDummy016 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_059`. -/
@[expose]
noncomputable def nb095AlphaDummy059 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_060`. -/
@[expose]
noncomputable def nb095AlphaDummy060 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCphi (Class.cv (nb095AlphaDummy058 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_061`. -/
@[expose]
noncomputable def nb095AlphaDummy061 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy055 D R S_cls E)
          (synWrex (nb095AlphaDummy056 D R S_cls E)
            (Class.cv (nb095AlphaDummy011 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy055 D R S_cls E)
          (synWrex (nb095AlphaDummy056 D R S_cls E)
            (Class.cv (nb095AlphaDummy011 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_062`. -/
@[expose]
noncomputable def nb095AlphaDummy062 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy057 f)
          (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
              (synCphi (Class.cv (nb095AlphaDummy058 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy057 f)
          (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
              (synCphi (Class.cv (nb095AlphaDummy058 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_063`. -/
@[expose]
noncomputable def nb095AlphaDummy063 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_064`. -/
@[expose]
noncomputable def nb095AlphaDummy064 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_065`. -/
@[expose]
noncomputable def nb095AlphaDummy065 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy058 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_066`. -/
@[expose]
noncomputable def nb095AlphaDummy066 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy058 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_067`. -/
@[expose]
noncomputable def nb095AlphaDummy067 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy063 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy063 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_068`. -/
@[expose]
noncomputable def nb095AlphaDummy068 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy065 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy065 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy065 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_069`. -/
@[expose]
noncomputable def nb095AlphaDummy069 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_070`. -/
@[expose]
noncomputable def nb095AlphaDummy070 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_071`. -/
@[expose]
noncomputable def nb095AlphaDummy071 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_072`. -/
@[expose]
noncomputable def nb095AlphaDummy072 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_073`. -/
@[expose]
noncomputable def nb095AlphaDummy073 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_074`. -/
@[expose]
noncomputable def nb095AlphaDummy074 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_075`. -/
@[expose]
noncomputable def nb095AlphaDummy075 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy070 D R S_cls E))
          (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy070 D R S_cls E))
          (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_076`. -/
@[expose]
noncomputable def nb095AlphaDummy076 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy073 f))
          (Class.cv (nb095AlphaDummy074 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy073 f)) (Class.cv (nb095AlphaDummy074 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_077`. -/
@[expose]
noncomputable def nb095AlphaDummy077 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_078`. -/
@[expose]
noncomputable def nb095AlphaDummy078 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy073 f))).fv ∪
      ((Class.cv (nb095AlphaDummy074 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_079`. -/
@[expose]
noncomputable def nb095AlphaDummy079 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy070 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy071 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_080`. -/
@[expose]
noncomputable def nb095AlphaDummy080 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy073 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy074 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_081`. -/
@[expose]
noncomputable def nb095AlphaDummy081 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_082`. -/
@[expose]
noncomputable def nb095AlphaDummy082 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy073 f))).fv ∪
      ((Class.cv (nb095AlphaDummy073 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_083`. -/
@[expose]
noncomputable def nb095AlphaDummy083 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_084`. -/
@[expose]
noncomputable def nb095AlphaDummy084 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy074 f))).fv ∪
      ((Class.cv (nb095AlphaDummy074 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_085`. -/
@[expose]
noncomputable def nb095AlphaDummy085 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy055 D R S_cls E)
          (synWrex (nb095AlphaDummy056 D R S_cls E)
            (Class.cv (nb095AlphaDummy013 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy055 D R S_cls E)
          (synWrex (nb095AlphaDummy056 D R S_cls E)
            (Class.cv (nb095AlphaDummy013 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_086`. -/
@[expose]
noncomputable def nb095AlphaDummy086 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy057 f)
          (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy057 f)
          (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy016 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy058 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_087`. -/
@[expose]
noncomputable def nb095AlphaDummy087 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_088`. -/
@[expose]
noncomputable def nb095AlphaDummy088 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy058 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_089`. -/
@[expose]
noncomputable def nb095AlphaDummy089 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_090`. -/
@[expose]
noncomputable def nb095AlphaDummy090 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy058 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy058 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_091`. -/
@[expose]
noncomputable def nb095AlphaDummy091 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_092`. -/
@[expose]
noncomputable def nb095AlphaDummy092 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_093`. -/
@[expose]
noncomputable def nb095AlphaDummy093 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_094`. -/
@[expose]
noncomputable def nb095AlphaDummy094 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_095`. -/
@[expose]
noncomputable def nb095AlphaDummy095 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy091 D R S_cls E)} : Finset Var) ∪
        ({(nb095AlphaDummy092 D R S_cls E)} : Finset Var) ∪
      ((synWbr (Class.cv (nb095AlphaDummy092 D R S_cls E))
          (Class.cv (nb095AlphaDummy000 D R S_cls E))
          (Class.cv (nb095AlphaDummy091 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_096`. -/
@[expose]
noncomputable def nb095AlphaDummy096 (f : Var) : Var :=
  (freshVar (({(nb095AlphaDummy093 f)} : Finset Var) ∪
        ({(nb095AlphaDummy094 f)} : Finset Var) ∪
      ((synWbr (Class.cv (nb095AlphaDummy094 f)) (Class.cv f)
          (Class.cv (nb095AlphaDummy093 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_097`. -/
@[expose]
noncomputable def nb095AlphaDummy097 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_098`. -/
@[expose]
noncomputable def nb095AlphaDummy098 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_099`. -/
@[expose]
noncomputable def nb095AlphaDummy099 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy093 f))).fv ∪
      ((Class.cv (nb095AlphaDummy094 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_100`. -/
@[expose]
noncomputable def nb095AlphaDummy100 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy093 f))).fv ∪
      ((Class.cv (nb095AlphaDummy094 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_101`. -/
@[expose]
noncomputable def nb095AlphaDummy101 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_102`. -/
@[expose]
noncomputable def nb095AlphaDummy102 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_103`. -/
@[expose]
noncomputable def nb095AlphaDummy103 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy097 D R S_cls E)
          (synWrex (nb095AlphaDummy098 D R S_cls E)
            (Class.cv (nb095AlphaDummy091 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy097 D R S_cls E)
          (synWrex (nb095AlphaDummy098 D R S_cls E)
            (Class.cv (nb095AlphaDummy091 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_104`. -/
@[expose]
noncomputable def nb095AlphaDummy104 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy099 f)
          (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
              (synCphi (Class.cv (nb095AlphaDummy100 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy099 f)
          (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
              (synCphi (Class.cv (nb095AlphaDummy100 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_105`. -/
@[expose]
noncomputable def nb095AlphaDummy105 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_106`. -/
@[expose]
noncomputable def nb095AlphaDummy106 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_107`. -/
@[expose]
noncomputable def nb095AlphaDummy107 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy100 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_108`. -/
@[expose]
noncomputable def nb095AlphaDummy108 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy100 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_109`. -/
@[expose]
noncomputable def nb095AlphaDummy109 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy105 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy105 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_110`. -/
@[expose]
noncomputable def nb095AlphaDummy110 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy107 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy107 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy107 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_111`. -/
@[expose]
noncomputable def nb095AlphaDummy111 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_112`. -/
@[expose]
noncomputable def nb095AlphaDummy112 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_113`. -/
@[expose]
noncomputable def nb095AlphaDummy113 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_114`. -/
@[expose]
noncomputable def nb095AlphaDummy114 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_115`. -/
@[expose]
noncomputable def nb095AlphaDummy115 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_116`. -/
@[expose]
noncomputable def nb095AlphaDummy116 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_117`. -/
@[expose]
noncomputable def nb095AlphaDummy117 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy112 D R S_cls E))
          (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy112 D R S_cls E))
          (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_118`. -/
@[expose]
noncomputable def nb095AlphaDummy118 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy115 f))
          (Class.cv (nb095AlphaDummy116 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy115 f)) (Class.cv (nb095AlphaDummy116 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_119`. -/
@[expose]
noncomputable def nb095AlphaDummy119 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_120`. -/
@[expose]
noncomputable def nb095AlphaDummy120 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy115 f))).fv ∪
      ((Class.cv (nb095AlphaDummy116 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_121`. -/
@[expose]
noncomputable def nb095AlphaDummy121 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy112 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy113 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_122`. -/
@[expose]
noncomputable def nb095AlphaDummy122 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy115 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy116 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_123`. -/
@[expose]
noncomputable def nb095AlphaDummy123 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_124`. -/
@[expose]
noncomputable def nb095AlphaDummy124 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy115 f))).fv ∪
      ((Class.cv (nb095AlphaDummy115 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_125`. -/
@[expose]
noncomputable def nb095AlphaDummy125 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_126`. -/
@[expose]
noncomputable def nb095AlphaDummy126 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy116 f))).fv ∪
      ((Class.cv (nb095AlphaDummy116 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_127`. -/
@[expose]
noncomputable def nb095AlphaDummy127 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy097 D R S_cls E)
          (synWrex (nb095AlphaDummy098 D R S_cls E)
            (Class.cv (nb095AlphaDummy092 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy097 D R S_cls E)
          (synWrex (nb095AlphaDummy098 D R S_cls E)
            (Class.cv (nb095AlphaDummy092 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_128`. -/
@[expose]
noncomputable def nb095AlphaDummy128 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy099 f)
          (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy099 f)
          (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy094 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy100 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_129`. -/
@[expose]
noncomputable def nb095AlphaDummy129 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_130`. -/
@[expose]
noncomputable def nb095AlphaDummy130 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy100 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_131`. -/
@[expose]
noncomputable def nb095AlphaDummy131 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_132`. -/
@[expose]
noncomputable def nb095AlphaDummy132 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy100 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy100 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_133`. -/
@[expose]
noncomputable def nb095AlphaDummy133 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_134`. -/
@[expose]
noncomputable def nb095AlphaDummy134 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_135`. -/
@[expose]
noncomputable def nb095AlphaDummy135 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy094 f))).fv ∪
      ((Class.cv (nb095AlphaDummy093 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_136`. -/
@[expose]
noncomputable def nb095AlphaDummy136 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy094 f))).fv ∪
      ((Class.cv (nb095AlphaDummy093 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_137`. -/
@[expose]
noncomputable def nb095AlphaDummy137 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_138`. -/
@[expose]
noncomputable def nb095AlphaDummy138 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCphi (Class.cv (nb095AlphaDummy136 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_139`. -/
@[expose]
noncomputable def nb095AlphaDummy139 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy133 D R S_cls E)
          (synWrex (nb095AlphaDummy134 D R S_cls E)
            (Class.cv (nb095AlphaDummy092 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy133 D R S_cls E)
          (synWrex (nb095AlphaDummy134 D R S_cls E)
            (Class.cv (nb095AlphaDummy092 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_140`. -/
@[expose]
noncomputable def nb095AlphaDummy140 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy135 f)
          (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
              (synCphi (Class.cv (nb095AlphaDummy136 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy135 f)
          (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
              (synCphi (Class.cv (nb095AlphaDummy136 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_141`. -/
@[expose]
noncomputable def nb095AlphaDummy141 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_142`. -/
@[expose]
noncomputable def nb095AlphaDummy142 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_143`. -/
@[expose]
noncomputable def nb095AlphaDummy143 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy136 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_144`. -/
@[expose]
noncomputable def nb095AlphaDummy144 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy136 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_145`. -/
@[expose]
noncomputable def nb095AlphaDummy145 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy141 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy141 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_146`. -/
@[expose]
noncomputable def nb095AlphaDummy146 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy143 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy143 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy143 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_147`. -/
@[expose]
noncomputable def nb095AlphaDummy147 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_148`. -/
@[expose]
noncomputable def nb095AlphaDummy148 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_149`. -/
@[expose]
noncomputable def nb095AlphaDummy149 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_150`. -/
@[expose]
noncomputable def nb095AlphaDummy150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_151`. -/
@[expose]
noncomputable def nb095AlphaDummy151 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_152`. -/
@[expose]
noncomputable def nb095AlphaDummy152 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_153`. -/
@[expose]
noncomputable def nb095AlphaDummy153 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy148 D R S_cls E))
          (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy148 D R S_cls E))
          (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_154`. -/
@[expose]
noncomputable def nb095AlphaDummy154 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy151 f))
          (Class.cv (nb095AlphaDummy152 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy151 f)) (Class.cv (nb095AlphaDummy152 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_155`. -/
@[expose]
noncomputable def nb095AlphaDummy155 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_156`. -/
@[expose]
noncomputable def nb095AlphaDummy156 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy151 f))).fv ∪
      ((Class.cv (nb095AlphaDummy152 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_157`. -/
@[expose]
noncomputable def nb095AlphaDummy157 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy148 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy149 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_158`. -/
@[expose]
noncomputable def nb095AlphaDummy158 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy151 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy152 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_159`. -/
@[expose]
noncomputable def nb095AlphaDummy159 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_160`. -/
@[expose]
noncomputable def nb095AlphaDummy160 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy151 f))).fv ∪
      ((Class.cv (nb095AlphaDummy151 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_161`. -/
@[expose]
noncomputable def nb095AlphaDummy161 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_162`. -/
@[expose]
noncomputable def nb095AlphaDummy162 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy152 f))).fv ∪
      ((Class.cv (nb095AlphaDummy152 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_163`. -/
@[expose]
noncomputable def nb095AlphaDummy163 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy133 D R S_cls E)
          (synWrex (nb095AlphaDummy134 D R S_cls E)
            (Class.cv (nb095AlphaDummy091 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy133 D R S_cls E)
          (synWrex (nb095AlphaDummy134 D R S_cls E)
            (Class.cv (nb095AlphaDummy091 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_164`. -/
@[expose]
noncomputable def nb095AlphaDummy164 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy135 f)
          (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy135 f)
          (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy093 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy136 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_165`. -/
@[expose]
noncomputable def nb095AlphaDummy165 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_166`. -/
@[expose]
noncomputable def nb095AlphaDummy166 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy136 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_167`. -/
@[expose]
noncomputable def nb095AlphaDummy167 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_168`. -/
@[expose]
noncomputable def nb095AlphaDummy168 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy136 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy136 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_169`. -/
@[expose]
noncomputable def nb095AlphaDummy169 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_170`. -/
@[expose]
noncomputable def nb095AlphaDummy170 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_171`. -/
@[expose]
noncomputable def nb095AlphaDummy171 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy016 f))).fv ∪
      ((Class.cv (nb095AlphaDummy015 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_172`. -/
@[expose]
noncomputable def nb095AlphaDummy172 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy016 f))).fv ∪
      ((Class.cv (nb095AlphaDummy015 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_173`. -/
@[expose]
noncomputable def nb095AlphaDummy173 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_174`. -/
@[expose]
noncomputable def nb095AlphaDummy174 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCphi (Class.cv (nb095AlphaDummy172 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_175`. -/
@[expose]
noncomputable def nb095AlphaDummy175 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy169 D R S_cls E)
          (synWrex (nb095AlphaDummy170 D R S_cls E)
            (Class.cv (nb095AlphaDummy013 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy169 D R S_cls E)
          (synWrex (nb095AlphaDummy170 D R S_cls E)
            (Class.cv (nb095AlphaDummy013 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_176`. -/
@[expose]
noncomputable def nb095AlphaDummy176 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy171 f)
          (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
              (synCphi (Class.cv (nb095AlphaDummy172 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy171 f)
          (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
              (synCphi (Class.cv (nb095AlphaDummy172 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_177`. -/
@[expose]
noncomputable def nb095AlphaDummy177 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_178`. -/
@[expose]
noncomputable def nb095AlphaDummy178 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_179`. -/
@[expose]
noncomputable def nb095AlphaDummy179 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy172 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_180`. -/
@[expose]
noncomputable def nb095AlphaDummy180 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy172 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_181`. -/
@[expose]
noncomputable def nb095AlphaDummy181 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy177 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy177 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_182`. -/
@[expose]
noncomputable def nb095AlphaDummy182 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy179 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy179 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy179 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_183`. -/
@[expose]
noncomputable def nb095AlphaDummy183 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_184`. -/
@[expose]
noncomputable def nb095AlphaDummy184 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_185`. -/
@[expose]
noncomputable def nb095AlphaDummy185 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_186`. -/
@[expose]
noncomputable def nb095AlphaDummy186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_187`. -/
@[expose]
noncomputable def nb095AlphaDummy187 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_188`. -/
@[expose]
noncomputable def nb095AlphaDummy188 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_189`. -/
@[expose]
noncomputable def nb095AlphaDummy189 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy184 D R S_cls E))
          (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy184 D R S_cls E))
          (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_190`. -/
@[expose]
noncomputable def nb095AlphaDummy190 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy187 f))
          (Class.cv (nb095AlphaDummy188 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy187 f)) (Class.cv (nb095AlphaDummy188 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_191`. -/
@[expose]
noncomputable def nb095AlphaDummy191 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_192`. -/
@[expose]
noncomputable def nb095AlphaDummy192 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy187 f))).fv ∪
      ((Class.cv (nb095AlphaDummy188 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_193`. -/
@[expose]
noncomputable def nb095AlphaDummy193 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy184 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy185 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_194`. -/
@[expose]
noncomputable def nb095AlphaDummy194 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy187 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy188 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_195`. -/
@[expose]
noncomputable def nb095AlphaDummy195 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_196`. -/
@[expose]
noncomputable def nb095AlphaDummy196 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy187 f))).fv ∪
      ((Class.cv (nb095AlphaDummy187 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_197`. -/
@[expose]
noncomputable def nb095AlphaDummy197 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_198`. -/
@[expose]
noncomputable def nb095AlphaDummy198 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy188 f))).fv ∪
      ((Class.cv (nb095AlphaDummy188 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_199`. -/
@[expose]
noncomputable def nb095AlphaDummy199 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy169 D R S_cls E)
          (synWrex (nb095AlphaDummy170 D R S_cls E)
            (Class.cv (nb095AlphaDummy012 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy169 D R S_cls E)
          (synWrex (nb095AlphaDummy170 D R S_cls E)
            (Class.cv (nb095AlphaDummy012 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_200`. -/
@[expose]
noncomputable def nb095AlphaDummy200 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy171 f)
          (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy171 f)
          (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy015 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy172 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_201`. -/
@[expose]
noncomputable def nb095AlphaDummy201 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_202`. -/
@[expose]
noncomputable def nb095AlphaDummy202 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy172 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_203`. -/
@[expose]
noncomputable def nb095AlphaDummy203 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_204`. -/
@[expose]
noncomputable def nb095AlphaDummy204 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy172 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy172 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_205`. -/
@[expose]
noncomputable def nb095AlphaDummy205 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_206`. -/
@[expose]
noncomputable def nb095AlphaDummy206 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_207`. -/
@[expose]
noncomputable def nb095AlphaDummy207 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_208`. -/
@[expose]
noncomputable def nb095AlphaDummy208 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_209`. -/
@[expose]
noncomputable def nb095AlphaDummy209 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_210`. -/
@[expose]
noncomputable def nb095AlphaDummy210 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_211`. -/
@[expose]
noncomputable def nb095AlphaDummy211 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy208 f))).fv ∪
      ((Class.cv (nb095AlphaDummy207 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_212`. -/
@[expose]
noncomputable def nb095AlphaDummy212 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy208 f))).fv ∪
      ((Class.cv (nb095AlphaDummy207 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_213`. -/
@[expose]
noncomputable def nb095AlphaDummy213 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy209 D R S_cls E)
            (synWrex (nb095AlphaDummy210 D R S_cls E)
              (Class.cv (nb095AlphaDummy205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_214`. -/
@[expose]
noncomputable def nb095AlphaDummy214 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCphi (Class.cv (nb095AlphaDummy212 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy211 f)
            (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_215`. -/
@[expose]
noncomputable def nb095AlphaDummy215 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy209 D R S_cls E)
          (synWrex (nb095AlphaDummy210 D R S_cls E)
            (Class.cv (nb095AlphaDummy206 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy209 D R S_cls E)
          (synWrex (nb095AlphaDummy210 D R S_cls E)
            (Class.cv (nb095AlphaDummy206 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_216`. -/
@[expose]
noncomputable def nb095AlphaDummy216 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy211 f)
          (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
              (synCphi (Class.cv (nb095AlphaDummy212 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy211 f)
          (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy208 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
              (synCphi (Class.cv (nb095AlphaDummy212 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_217`. -/
@[expose]
noncomputable def nb095AlphaDummy217 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_218`. -/
@[expose]
noncomputable def nb095AlphaDummy218 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_219`. -/
@[expose]
noncomputable def nb095AlphaDummy219 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy212 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_220`. -/
@[expose]
noncomputable def nb095AlphaDummy220 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy212 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_221`. -/
@[expose]
noncomputable def nb095AlphaDummy221 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy217 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy217 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_222`. -/
@[expose]
noncomputable def nb095AlphaDummy222 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy219 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy219 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy219 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_223`. -/
@[expose]
noncomputable def nb095AlphaDummy223 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_224`. -/
@[expose]
noncomputable def nb095AlphaDummy224 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_225`. -/
@[expose]
noncomputable def nb095AlphaDummy225 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_226`. -/
@[expose]
noncomputable def nb095AlphaDummy226 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_227`. -/
@[expose]
noncomputable def nb095AlphaDummy227 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_228`. -/
@[expose]
noncomputable def nb095AlphaDummy228 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_229`. -/
@[expose]
noncomputable def nb095AlphaDummy229 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy224 D R S_cls E))
          (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy224 D R S_cls E))
          (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_230`. -/
@[expose]
noncomputable def nb095AlphaDummy230 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy227 f))
          (Class.cv (nb095AlphaDummy228 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy227 f)) (Class.cv (nb095AlphaDummy228 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_231`. -/
@[expose]
noncomputable def nb095AlphaDummy231 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_232`. -/
@[expose]
noncomputable def nb095AlphaDummy232 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy227 f))).fv ∪
      ((Class.cv (nb095AlphaDummy228 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_233`. -/
@[expose]
noncomputable def nb095AlphaDummy233 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy224 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy225 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_234`. -/
@[expose]
noncomputable def nb095AlphaDummy234 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy227 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy228 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_235`. -/
@[expose]
noncomputable def nb095AlphaDummy235 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_236`. -/
@[expose]
noncomputable def nb095AlphaDummy236 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy227 f))).fv ∪
      ((Class.cv (nb095AlphaDummy227 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_237`. -/
@[expose]
noncomputable def nb095AlphaDummy237 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_238`. -/
@[expose]
noncomputable def nb095AlphaDummy238 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy228 f))).fv ∪
      ((Class.cv (nb095AlphaDummy228 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_239`. -/
@[expose]
noncomputable def nb095AlphaDummy239 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy209 D R S_cls E)
          (synWrex (nb095AlphaDummy210 D R S_cls E)
            (Class.cv (nb095AlphaDummy205 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy209 D R S_cls E)
          (synWrex (nb095AlphaDummy210 D R S_cls E)
            (Class.cv (nb095AlphaDummy205 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy209 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_240`. -/
@[expose]
noncomputable def nb095AlphaDummy240 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy211 f)
          (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy211 f)
          (synWrex (nb095AlphaDummy212 f) (Class.cv (nb095AlphaDummy207 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy211 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy212 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_241`. -/
@[expose]
noncomputable def nb095AlphaDummy241 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_242`. -/
@[expose]
noncomputable def nb095AlphaDummy242 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy212 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_243`. -/
@[expose]
noncomputable def nb095AlphaDummy243 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy210 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_244`. -/
@[expose]
noncomputable def nb095AlphaDummy244 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy212 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy212 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_245`. -/
@[expose]
noncomputable def nb095AlphaDummy245 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCnin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_246`. -/
@[expose]
noncomputable def nb095AlphaDummy246 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCnin D
          (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
      ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_247`. -/
@[expose]
noncomputable def nb095AlphaDummy247 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_248`. -/
@[expose]
noncomputable def nb095AlphaDummy248 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar
    ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_249`. -/
@[expose]
noncomputable def nb095AlphaDummy249 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_250`. -/
@[expose]
noncomputable def nb095AlphaDummy250 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪
      ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_251`. -/
@[expose]
noncomputable def nb095AlphaDummy251 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn (Class.cv x))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_252`. -/
@[expose]
noncomputable def nb095AlphaDummy252 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn (Class.cv x))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_253`. -/
@[expose]
noncomputable def nb095AlphaDummy253 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy002 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_254`. -/
@[expose]
noncomputable def nb095AlphaDummy254 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_255`. -/
@[expose]
noncomputable def nb095AlphaDummy255 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_256`. -/
@[expose]
noncomputable def nb095AlphaDummy256 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_257`. -/
@[expose]
noncomputable def nb095AlphaDummy257 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
      ((Class.cv (nb095AlphaDummy251 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_258`. -/
@[expose]
noncomputable def nb095AlphaDummy258 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
      ((Class.cv (nb095AlphaDummy251 x R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_259`. -/
@[expose]
noncomputable def nb095AlphaDummy259 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_260`. -/
@[expose]
noncomputable def nb095AlphaDummy260 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCphi (Class.cv (nb095AlphaDummy258 x R)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_261`. -/
@[expose]
noncomputable def nb095AlphaDummy261 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy255 D R S_cls E)
          (synWrex (nb095AlphaDummy256 D R S_cls E)
            (Class.cv (nb095AlphaDummy250 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy255 D R S_cls E)
          (synWrex (nb095AlphaDummy256 D R S_cls E)
            (Class.cv (nb095AlphaDummy250 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_262`. -/
@[expose]
noncomputable def nb095AlphaDummy262 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy257 x R)
          (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
            (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
              (synCphi (Class.cv (nb095AlphaDummy258 x R))))))).fv ∪
      ((Class.cab (nb095AlphaDummy257 x R)
          (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
            (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
              (synCphi (Class.cv (nb095AlphaDummy258 x R))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_263`. -/
@[expose]
noncomputable def nb095AlphaDummy263 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_264`. -/
@[expose]
noncomputable def nb095AlphaDummy264 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_265`. -/
@[expose]
noncomputable def nb095AlphaDummy265 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy258 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_266`. -/
@[expose]
noncomputable def nb095AlphaDummy266 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy258 x R))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_267`. -/
@[expose]
noncomputable def nb095AlphaDummy267 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy263 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy263 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_268`. -/
@[expose]
noncomputable def nb095AlphaDummy268 (x : Var) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy265 x R)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy265 x R)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy265 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_269`. -/
@[expose]
noncomputable def nb095AlphaDummy269 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_270`. -/
@[expose]
noncomputable def nb095AlphaDummy270 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_271`. -/
@[expose]
noncomputable def nb095AlphaDummy271 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_272`. -/
@[expose]
noncomputable def nb095AlphaDummy272 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_273`. -/
@[expose]
noncomputable def nb095AlphaDummy273 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_274`. -/
@[expose]
noncomputable def nb095AlphaDummy274 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_275`. -/
@[expose]
noncomputable def nb095AlphaDummy275 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy270 D R S_cls E))
          (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy270 D R S_cls E))
          (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_276`. -/
@[expose]
noncomputable def nb095AlphaDummy276 (x : Var) (R : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy273 x R))
          (Class.cv (nb095AlphaDummy274 x R)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy273 x R))
          (Class.cv (nb095AlphaDummy274 x R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_277`. -/
@[expose]
noncomputable def nb095AlphaDummy277 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_278`. -/
@[expose]
noncomputable def nb095AlphaDummy278 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy273 x R))).fv ∪
      ((Class.cv (nb095AlphaDummy274 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_279`. -/
@[expose]
noncomputable def nb095AlphaDummy279 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy270 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy271 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_280`. -/
@[expose]
noncomputable def nb095AlphaDummy280 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy273 x R)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy274 x R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_281`. -/
@[expose]
noncomputable def nb095AlphaDummy281 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_282`. -/
@[expose]
noncomputable def nb095AlphaDummy282 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy273 x R))).fv ∪
      ((Class.cv (nb095AlphaDummy273 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_283`. -/
@[expose]
noncomputable def nb095AlphaDummy283 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_284`. -/
@[expose]
noncomputable def nb095AlphaDummy284 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy274 x R))).fv ∪
      ((Class.cv (nb095AlphaDummy274 x R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_285`. -/
@[expose]
noncomputable def nb095AlphaDummy285 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy255 D R S_cls E)
          (synWrex (nb095AlphaDummy256 D R S_cls E)
            (Class.cv (nb095AlphaDummy249 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy255 D R S_cls E)
          (synWrex (nb095AlphaDummy256 D R S_cls E)
            (Class.cv (nb095AlphaDummy249 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_286`. -/
@[expose]
noncomputable def nb095AlphaDummy286 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy257 x R)
          (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
            (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
              (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy257 x R)
          (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy251 x R))
            (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
              (synCun (synCphi (Class.cv (nb095AlphaDummy258 x R)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_287`. -/
@[expose]
noncomputable def nb095AlphaDummy287 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_288`. -/
@[expose]
noncomputable def nb095AlphaDummy288 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy258 x R))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_289`. -/
@[expose]
noncomputable def nb095AlphaDummy289 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_290`. -/
@[expose]
noncomputable def nb095AlphaDummy290 (x : Var) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy258 x R)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy258 x R)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_291`. -/
@[expose]
noncomputable def nb095AlphaDummy291 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv ∪
      ((synCnin (synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_292`. -/
@[expose]
noncomputable def nb095AlphaDummy292 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    Var :=
  (freshVar (((synCnin (synCrn (Class.cv f)) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv ∪
      ((synCnin (synCrn (Class.cv f)) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_293`. -/
@[expose]
noncomputable def nb095AlphaDummy293 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCrn (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_294`. -/
@[expose]
noncomputable def nb095AlphaDummy294 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    Var :=
  (freshVar (((synCrn (Class.cv f))).fv ∪ ((synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_295`. -/
@[expose]
noncomputable def nb095AlphaDummy295 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_296`. -/
@[expose]
noncomputable def nb095AlphaDummy296 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_297`. -/
@[expose]
noncomputable def nb095AlphaDummy297 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_298`. -/
@[expose]
noncomputable def nb095AlphaDummy298 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_299`. -/
@[expose]
noncomputable def nb095AlphaDummy299 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) 0)

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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_300`. -/
@[expose]
noncomputable def nb095AlphaDummy300 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_301`. -/
@[expose]
noncomputable def nb095AlphaDummy301 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy298 f))).fv ∪
      ((Class.cv (nb095AlphaDummy297 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_302`. -/
@[expose]
noncomputable def nb095AlphaDummy302 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy298 f))).fv ∪
      ((Class.cv (nb095AlphaDummy297 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_303`. -/
@[expose]
noncomputable def nb095AlphaDummy303 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_304`. -/
@[expose]
noncomputable def nb095AlphaDummy304 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCphi (Class.cv (nb095AlphaDummy302 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_305`. -/
@[expose]
noncomputable def nb095AlphaDummy305 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy299 D R S_cls E)
          (synWrex (nb095AlphaDummy300 D R S_cls E)
            (Class.cv (nb095AlphaDummy296 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy299 D R S_cls E)
          (synWrex (nb095AlphaDummy300 D R S_cls E)
            (Class.cv (nb095AlphaDummy296 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_306`. -/
@[expose]
noncomputable def nb095AlphaDummy306 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy301 f)
          (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
              (synCphi (Class.cv (nb095AlphaDummy302 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy301 f)
          (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
              (synCphi (Class.cv (nb095AlphaDummy302 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_307`. -/
@[expose]
noncomputable def nb095AlphaDummy307 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_308`. -/
@[expose]
noncomputable def nb095AlphaDummy308 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_309`. -/
@[expose]
noncomputable def nb095AlphaDummy309 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy302 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_310`. -/
@[expose]
noncomputable def nb095AlphaDummy310 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy302 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_311`. -/
@[expose]
noncomputable def nb095AlphaDummy311 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy307 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy307 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_312`. -/
@[expose]
noncomputable def nb095AlphaDummy312 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy309 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy309 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy309 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_313`. -/
@[expose]
noncomputable def nb095AlphaDummy313 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_314`. -/
@[expose]
noncomputable def nb095AlphaDummy314 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_315`. -/
@[expose]
noncomputable def nb095AlphaDummy315 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy307 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_316`. -/
@[expose]
noncomputable def nb095AlphaDummy316 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_317`. -/
@[expose]
noncomputable def nb095AlphaDummy317 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_318`. -/
@[expose]
noncomputable def nb095AlphaDummy318 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy309 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_319`. -/
@[expose]
noncomputable def nb095AlphaDummy319 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy314 D R S_cls E))
          (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy314 D R S_cls E))
          (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_320`. -/
@[expose]
noncomputable def nb095AlphaDummy320 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy317 f))
          (Class.cv (nb095AlphaDummy318 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy317 f)) (Class.cv (nb095AlphaDummy318 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_321`. -/
@[expose]
noncomputable def nb095AlphaDummy321 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_322`. -/
@[expose]
noncomputable def nb095AlphaDummy322 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy317 f))).fv ∪
      ((Class.cv (nb095AlphaDummy318 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_323`. -/
@[expose]
noncomputable def nb095AlphaDummy323 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy314 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy315 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_324`. -/
@[expose]
noncomputable def nb095AlphaDummy324 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy317 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy318 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_325`. -/
@[expose]
noncomputable def nb095AlphaDummy325 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy314 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_326`. -/
@[expose]
noncomputable def nb095AlphaDummy326 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy317 f))).fv ∪
      ((Class.cv (nb095AlphaDummy317 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_327`. -/
@[expose]
noncomputable def nb095AlphaDummy327 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy315 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_328`. -/
@[expose]
noncomputable def nb095AlphaDummy328 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy318 f))).fv ∪
      ((Class.cv (nb095AlphaDummy318 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_329`. -/
@[expose]
noncomputable def nb095AlphaDummy329 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy299 D R S_cls E)
          (synWrex (nb095AlphaDummy300 D R S_cls E)
            (Class.cv (nb095AlphaDummy295 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy299 D R S_cls E)
          (synWrex (nb095AlphaDummy300 D R S_cls E)
            (Class.cv (nb095AlphaDummy295 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_330`. -/
@[expose]
noncomputable def nb095AlphaDummy330 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy301 f)
          (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy301 f)
          (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_331`. -/
@[expose]
noncomputable def nb095AlphaDummy331 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_332`. -/
@[expose]
noncomputable def nb095AlphaDummy332 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy302 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_333`. -/
@[expose]
noncomputable def nb095AlphaDummy333 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_334`. -/
@[expose]
noncomputable def nb095AlphaDummy334 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy302 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy302 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_335`. -/
@[expose]
noncomputable def nb095AlphaDummy335 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCnin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_336`. -/
@[expose]
noncomputable def nb095AlphaDummy336 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((synCnin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
      ((synCnin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_337`. -/
@[expose]
noncomputable def nb095AlphaDummy337 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((E).fv ∪ ((synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_338`. -/
@[expose]
noncomputable def nb095AlphaDummy338 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar ((E).fv ∪
      ((synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_339`. -/
@[expose]
noncomputable def nb095AlphaDummy339 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (synCdif S_cls (synCid)))).fv ∪
      ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_340`. -/
@[expose]
noncomputable def nb095AlphaDummy340 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (synCdif S_cls (synCid)))).fv ∪
      ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_341`. -/
@[expose]
noncomputable def nb095AlphaDummy341 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_342`. -/
@[expose]
noncomputable def nb095AlphaDummy342 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn (Class.cv u))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_343`. -/
@[expose]
noncomputable def nb095AlphaDummy343 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy001 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_344`. -/
@[expose]
noncomputable def nb095AlphaDummy344 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_345`. -/
@[expose]
noncomputable def nb095AlphaDummy345 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_346`. -/
@[expose]
noncomputable def nb095AlphaDummy346 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy340 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_347`. -/
@[expose]
noncomputable def nb095AlphaDummy347 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
      ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_348`. -/
@[expose]
noncomputable def nb095AlphaDummy348 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪
      ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_349`. -/
@[expose]
noncomputable def nb095AlphaDummy349 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_350`. -/
@[expose]
noncomputable def nb095AlphaDummy350 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy347 u S_cls)
            (synWrex (nb095AlphaDummy348 u S_cls) (Class.cv (nb095AlphaDummy342 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy341 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_351`. -/
@[expose]
noncomputable def nb095AlphaDummy351 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy345 D R S_cls E)
          (synWrex (nb095AlphaDummy346 D R S_cls E)
            (Class.cv (nb095AlphaDummy340 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy345 D R S_cls E)
          (synWrex (nb095AlphaDummy346 D R S_cls E)
            (Class.cv (nb095AlphaDummy340 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_352`. -/
@[expose]
noncomputable def nb095AlphaDummy352 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy347 u S_cls)
          (synWrex (nb095AlphaDummy348 u S_cls) (Class.cv (nb095AlphaDummy342 u S_cls))
            (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
              (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))))).fv ∪
      ((Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
            (Class.cv (nb095AlphaDummy342 u S_cls))
            (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
              (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_353`. -/
@[expose]
noncomputable def nb095AlphaDummy353 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_354`. -/
@[expose]
noncomputable def nb095AlphaDummy354 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy346 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_355`. -/
@[expose]
noncomputable def nb095AlphaDummy355 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_356`. -/
@[expose]
noncomputable def nb095AlphaDummy356 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy348 u S_cls))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_357`. -/
@[expose]
noncomputable def nb095AlphaDummy357 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy353 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy353 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_358`. -/
@[expose]
noncomputable def nb095AlphaDummy358 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy355 u S_cls)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy355 u S_cls)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy355 u S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_359`. -/
@[expose]
noncomputable def nb095AlphaDummy359 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_360`. -/
@[expose]
noncomputable def nb095AlphaDummy360 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_361`. -/
@[expose]
noncomputable def nb095AlphaDummy361 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy353 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_362`. -/
@[expose]
noncomputable def nb095AlphaDummy362 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_363`. -/
@[expose]
noncomputable def nb095AlphaDummy363 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_364`. -/
@[expose]
noncomputable def nb095AlphaDummy364 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy355 u S_cls))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_365`. -/
@[expose]
noncomputable def nb095AlphaDummy365 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy360 D R S_cls E))
          (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy360 D R S_cls E))
          (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_366`. -/
@[expose]
noncomputable def nb095AlphaDummy366 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy363 u S_cls))
          (Class.cv (nb095AlphaDummy364 u S_cls)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy363 u S_cls))
          (Class.cv (nb095AlphaDummy364 u S_cls)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_367`. -/
@[expose]
noncomputable def nb095AlphaDummy367 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_368`. -/
@[expose]
noncomputable def nb095AlphaDummy368 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy363 u S_cls))).fv ∪
      ((Class.cv (nb095AlphaDummy364 u S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_369`. -/
@[expose]
noncomputable def nb095AlphaDummy369 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy360 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy361 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_370`. -/
@[expose]
noncomputable def nb095AlphaDummy370 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy363 u S_cls)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy364 u S_cls)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_371`. -/
@[expose]
noncomputable def nb095AlphaDummy371 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy360 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_372`. -/
@[expose]
noncomputable def nb095AlphaDummy372 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy363 u S_cls))).fv ∪
      ((Class.cv (nb095AlphaDummy363 u S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_373`. -/
@[expose]
noncomputable def nb095AlphaDummy373 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy361 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_374`. -/
@[expose]
noncomputable def nb095AlphaDummy374 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy364 u S_cls))).fv ∪
      ((Class.cv (nb095AlphaDummy364 u S_cls))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_375`. -/
@[expose]
noncomputable def nb095AlphaDummy375 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy345 D R S_cls E)
          (synWrex (nb095AlphaDummy346 D R S_cls E)
            (Class.cv (nb095AlphaDummy339 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy345 D R S_cls E)
          (synWrex (nb095AlphaDummy346 D R S_cls E)
            (Class.cv (nb095AlphaDummy339 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_376`. -/
@[expose]
noncomputable def nb095AlphaDummy376 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy347 u S_cls)
          (synWrex (nb095AlphaDummy348 u S_cls) (Class.cv (nb095AlphaDummy341 u S_cls))
            (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
              (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy347 u S_cls)
          (synWrex (nb095AlphaDummy348 u S_cls) (Class.cv (nb095AlphaDummy341 u S_cls))
            (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
              (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_377`. -/
@[expose]
noncomputable def nb095AlphaDummy377 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_378`. -/
@[expose]
noncomputable def nb095AlphaDummy378 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_379`. -/
@[expose]
noncomputable def nb095AlphaDummy379 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_380`. -/
@[expose]
noncomputable def nb095AlphaDummy380 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_381`. -/
@[expose]
noncomputable def nb095AlphaDummy381 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))
          (synCid))).fv ∪ ((synCnin
          (synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
            (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))
          (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_382`. -/
@[expose]
noncomputable def nb095AlphaDummy382 (f : Var) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
          (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
          (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_383`. -/
@[expose]
noncomputable def nb095AlphaDummy383 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
          (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))))).fv ∪
      ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_384`. -/
@[expose]
noncomputable def nb095AlphaDummy384 (f : Var) : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))).fv ∪
      ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_385`. -/
@[expose]
noncomputable def nb095AlphaDummy385 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_386`. -/
@[expose]
noncomputable def nb095AlphaDummy386 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_387`. -/
@[expose]
noncomputable def nb095AlphaDummy387 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_388`. -/
@[expose]
noncomputable def nb095AlphaDummy388 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_389`. -/
@[expose]
noncomputable def nb095AlphaDummy389 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_390`. -/
@[expose]
noncomputable def nb095AlphaDummy390 (f : Var) : Var :=
  (freshVar (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_391`. -/
@[expose]
noncomputable def nb095AlphaDummy391 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095AlphaDummy385 D R S_cls E)} : Finset Var) ∪
        ({(nb095AlphaDummy386 D R S_cls E)} : Finset Var) ∪
      ((synWex (nb095AlphaDummy387 D R S_cls E) (synWa
            (synWbr (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))
              (Class.cv (nb095AlphaDummy387 D R S_cls E)))
            (synWbr (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
              (Class.cv (nb095AlphaDummy386 D R S_cls E)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_392`. -/
@[expose]
noncomputable def nb095AlphaDummy392 (f : Var) : Var :=
  (freshVar (({(nb095AlphaDummy388 f)} : Finset Var) ∪
        ({(nb095AlphaDummy389 f)} : Finset Var) ∪ ((synWex (nb095AlphaDummy390 f) (synWa
            (synWbr (Class.cv (nb095AlphaDummy388 f))
              (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb095AlphaDummy390 f)))
            (synWbr (Class.cv (nb095AlphaDummy390 f)) (synCcnv (Class.cv f))
              (Class.cv (nb095AlphaDummy389 f)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_393`. -/
@[expose]
noncomputable def nb095AlphaDummy393 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_394`. -/
@[expose]
noncomputable def nb095AlphaDummy394 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_395`. -/
@[expose]
noncomputable def nb095AlphaDummy395 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy388 f))).fv ∪
      ((Class.cv (nb095AlphaDummy389 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_396`. -/
@[expose]
noncomputable def nb095AlphaDummy396 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy388 f))).fv ∪
      ((Class.cv (nb095AlphaDummy389 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_397`. -/
@[expose]
noncomputable def nb095AlphaDummy397 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_398`. -/
@[expose]
noncomputable def nb095AlphaDummy398 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCphi (Class.cv (nb095AlphaDummy396 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_399`. -/
@[expose]
noncomputable def nb095AlphaDummy399 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy393 D R S_cls E)
          (synWrex (nb095AlphaDummy394 D R S_cls E)
            (Class.cv (nb095AlphaDummy385 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy393 D R S_cls E)
          (synWrex (nb095AlphaDummy394 D R S_cls E)
            (Class.cv (nb095AlphaDummy385 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_400`. -/
@[expose]
noncomputable def nb095AlphaDummy400 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy395 f)
          (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
              (synCphi (Class.cv (nb095AlphaDummy396 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy395 f)
          (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
              (synCphi (Class.cv (nb095AlphaDummy396 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_401`. -/
@[expose]
noncomputable def nb095AlphaDummy401 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_402`. -/
@[expose]
noncomputable def nb095AlphaDummy402 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy394 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_403`. -/
@[expose]
noncomputable def nb095AlphaDummy403 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy396 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_404`. -/
@[expose]
noncomputable def nb095AlphaDummy404 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy396 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_405`. -/
@[expose]
noncomputable def nb095AlphaDummy405 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy401 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy401 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_406`. -/
@[expose]
noncomputable def nb095AlphaDummy406 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy403 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy403 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy403 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_407`. -/
@[expose]
noncomputable def nb095AlphaDummy407 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_408`. -/
@[expose]
noncomputable def nb095AlphaDummy408 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_409`. -/
@[expose]
noncomputable def nb095AlphaDummy409 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy401 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_410`. -/
@[expose]
noncomputable def nb095AlphaDummy410 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_411`. -/
@[expose]
noncomputable def nb095AlphaDummy411 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_412`. -/
@[expose]
noncomputable def nb095AlphaDummy412 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy403 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_413`. -/
@[expose]
noncomputable def nb095AlphaDummy413 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
          (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy408 D R S_cls E))
          (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_414`. -/
@[expose]
noncomputable def nb095AlphaDummy414 (f : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy411 f))
          (Class.cv (nb095AlphaDummy412 f)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy411 f)) (Class.cv (nb095AlphaDummy412 f)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_415`. -/
@[expose]
noncomputable def nb095AlphaDummy415 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_416`. -/
@[expose]
noncomputable def nb095AlphaDummy416 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy411 f))).fv ∪
      ((Class.cv (nb095AlphaDummy412 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_417`. -/
@[expose]
noncomputable def nb095AlphaDummy417 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy408 D R S_cls E)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy409 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_418`. -/
@[expose]
noncomputable def nb095AlphaDummy418 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb095AlphaDummy411 f)))).fv ∪
      ((synCcompl (Class.cv (nb095AlphaDummy412 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_419`. -/
@[expose]
noncomputable def nb095AlphaDummy419 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy408 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_420`. -/
@[expose]
noncomputable def nb095AlphaDummy420 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy411 f))).fv ∪
      ((Class.cv (nb095AlphaDummy411 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_421`. -/
@[expose]
noncomputable def nb095AlphaDummy421 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy409 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_422`. -/
@[expose]
noncomputable def nb095AlphaDummy422 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy412 f))).fv ∪
      ((Class.cv (nb095AlphaDummy412 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_423`. -/
@[expose]
noncomputable def nb095AlphaDummy423 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy393 D R S_cls E)
          (synWrex (nb095AlphaDummy394 D R S_cls E)
            (Class.cv (nb095AlphaDummy386 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy393 D R S_cls E)
          (synWrex (nb095AlphaDummy394 D R S_cls E)
            (Class.cv (nb095AlphaDummy386 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_424`. -/
@[expose]
noncomputable def nb095AlphaDummy424 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy395 f)
          (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy395 f)
          (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
              (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_425`. -/
@[expose]
noncomputable def nb095AlphaDummy425 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_426`. -/
@[expose]
noncomputable def nb095AlphaDummy426 (f : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb095AlphaDummy396 f))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_427`. -/
@[expose]
noncomputable def nb095AlphaDummy427 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_428`. -/
@[expose]
noncomputable def nb095AlphaDummy428 (f : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy396 f)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy396 f)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_429`. -/
@[expose]
noncomputable def nb095AlphaDummy429 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_430`. -/
@[expose]
noncomputable def nb095AlphaDummy430 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
      ((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_431`. -/
@[expose]
noncomputable def nb095AlphaDummy431 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy388 f))).fv ∪
      ((Class.cv (nb095AlphaDummy390 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_432`. -/
@[expose]
noncomputable def nb095AlphaDummy432 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy388 f))).fv ∪
      ((Class.cv (nb095AlphaDummy390 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_433`. -/
@[expose]
noncomputable def nb095AlphaDummy433 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_434`. -/
@[expose]
noncomputable def nb095AlphaDummy434 (f : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCphi (Class.cv (nb095AlphaDummy432 f)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_435`. -/
@[expose]
noncomputable def nb095AlphaDummy435 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy429 D R S_cls E)
          (synWrex (nb095AlphaDummy430 D R S_cls E)
            (Class.cv (nb095AlphaDummy385 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095AlphaDummy429 D R S_cls E)
          (synWrex (nb095AlphaDummy430 D R S_cls E)
            (Class.cv (nb095AlphaDummy385 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
              (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_436`. -/
@[expose]
noncomputable def nb095AlphaDummy436 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy431 f)
          (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
              (synCphi (Class.cv (nb095AlphaDummy432 f))))))).fv ∪
      ((Class.cab (nb095AlphaDummy431 f)
          (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
            (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
              (synCphi (Class.cv (nb095AlphaDummy432 f))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_437`. -/
@[expose]
noncomputable def nb095AlphaDummy437 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_438`. -/
@[expose]
noncomputable def nb095AlphaDummy438 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_439`. -/
@[expose]
noncomputable def nb095AlphaDummy439 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy432 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_440`. -/
@[expose]
noncomputable def nb095AlphaDummy440 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy432 f))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_441`. -/
@[expose]
noncomputable def nb095AlphaDummy441 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy437 D R S_cls E)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy437 D R S_cls E)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_442`. -/
@[expose]
noncomputable def nb095AlphaDummy442 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095AlphaDummy439 f)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb095AlphaDummy439 f)) (synC1c))).fv ∪
      ((Class.cv (nb095AlphaDummy439 f))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_443`. -/
@[expose]
noncomputable def nb095AlphaDummy443 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_444`. -/
@[expose]
noncomputable def nb095AlphaDummy444 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_445`. -/
@[expose]
noncomputable def nb095AlphaDummy445 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_446`. -/
@[expose]
noncomputable def nb095AlphaDummy446 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_447`. -/
@[expose]
noncomputable def nb095AlphaDummy447 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_448`. -/
@[expose]
noncomputable def nb095AlphaDummy448 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_449`. -/
@[expose]
noncomputable def nb095AlphaDummy449 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
          (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv ∪
      ((synCnin (Class.cv (nb095AlphaDummy444 D R S_cls E))
          (Class.cv (nb095AlphaDummy445 D R S_cls E)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
