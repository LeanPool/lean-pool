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

@[expose]
noncomputable def nb095_alpha_dummy_000 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_001 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_002 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_003 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
          ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_004 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
          ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_005 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
      ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_006 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
      ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
    1)

@[expose]
noncomputable def nb095_alpha_dummy_007 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_008 (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_009 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccom (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
          (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_010 (f : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_011 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
      ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_012 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
      ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_013 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
      ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_014 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_015 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_016 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_017 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_011 D R S_cls E)} : Finset Var) ∪
        ({(nb095_alpha_dummy_012 D R S_cls E)} : Finset Var) ∪
      ((syn_wex (nb095_alpha_dummy_013 D R S_cls E) (syn_wa
            (syn_wbr (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E)))
            (syn_wbr (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_018 (f : Var) : Var :=
  (freshVar (({(nb095_alpha_dummy_014 f)} : Finset Var) ∪
        ({(nb095_alpha_dummy_015 f)} : Finset Var) ∪ ((syn_wex (nb095_alpha_dummy_016 f) (syn_wa
            (syn_wbr (Class.cv (nb095_alpha_dummy_014 f)) (syn_ccnv (Class.cv f))
              (Class.cv (nb095_alpha_dummy_016 f)))
            (syn_wbr (Class.cv (nb095_alpha_dummy_016 f)) (Class.cv f)
              (Class.cv (nb095_alpha_dummy_015 f)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_019 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_020 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_021 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_015 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_022 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_015 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_023 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_024 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_025 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_026 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_021 f)
          (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_021 f)
          (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_027 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_028 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_029 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_022 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_030 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_022 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_031 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_027 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_027 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_032 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_029 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_029 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_029 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_033 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_034 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_035 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_036 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_037 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_038 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_039 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_034 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_040 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_037 f))
          (Class.cv (nb095_alpha_dummy_038 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_037 f)) (Class.cv (nb095_alpha_dummy_038 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_041 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_042 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_038 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_043 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_034 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_035 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_044 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_037 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_038 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_045 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_046 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_037 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_047 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_048 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_038 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_038 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_049 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_019 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_050 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_021 f)
          (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_021 f)
          (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_015 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_051 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_052 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_053 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_054 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_022 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_055 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_056 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_057 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_016 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_058 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_016 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_059 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_055 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_060 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_057 f)
            (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_061 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_062 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_057 f)
          (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_057 f)
          (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_014 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_063 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_064 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_065 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_058 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_066 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_058 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_067 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_063 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_063 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_068 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_065 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_065 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_065 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_069 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_070 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_071 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_072 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_073 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_074 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_075 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_070 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_076 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_073 f))
          (Class.cv (nb095_alpha_dummy_074 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_073 f)) (Class.cv (nb095_alpha_dummy_074 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_077 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_078 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_074 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_079 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_070 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_071 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_080 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_073 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_074 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_081 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_082 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_073 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_083 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_084 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_074 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_074 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_085 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_055 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_056 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_055 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_086 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_057 f)
          (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_057 f)
          (syn_wrex (nb095_alpha_dummy_058 f) (Class.cv (nb095_alpha_dummy_016 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_057 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_087 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_088 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_089 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_090 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_058 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_091 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_092 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_093 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_094 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_095 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_091 D R S_cls E)} : Finset Var) ∪
        ({(nb095_alpha_dummy_092 D R S_cls E)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_091 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_096 (f : Var) : Var :=
  (freshVar (({(nb095_alpha_dummy_093 f)} : Finset Var) ∪
        ({(nb095_alpha_dummy_094 f)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb095_alpha_dummy_094 f)) (Class.cv f)
          (Class.cv (nb095_alpha_dummy_093 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_097 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_098 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_099 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_094 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_100 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_094 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_101 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_102 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_103 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_104 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_099 f)
          (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_099 f)
          (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_105 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_106 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_107 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_100 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_108 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_100 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_109 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_105 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_105 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_110 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_107 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_107 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_107 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_111 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_112 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_113 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_114 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_115 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_116 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_117 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_112 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_118 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_115 f))
          (Class.cv (nb095_alpha_dummy_116 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_115 f)) (Class.cv (nb095_alpha_dummy_116 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_119 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_120 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_116 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_121 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_112 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_113 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_122 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_115 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_116 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_123 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_124 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_115 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_125 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_126 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_116 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_116 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_127 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_097 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_128 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_099 f)
          (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_099 f)
          (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_094 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_129 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_130 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_131 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_132 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_133 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_134 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_135 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_093 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_136 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_093 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_137 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_138 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_139 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_140 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_135 f)
          (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_135 f)
          (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_141 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_142 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_143 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_136 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_144 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_136 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_145 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_141 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_141 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_146 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_143 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_143 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_143 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_147 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_148 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_149 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

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

@[expose]
noncomputable def nb095_alpha_dummy_150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_151 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_152 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_153 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_148 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_154 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_151 f))
          (Class.cv (nb095_alpha_dummy_152 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_151 f)) (Class.cv (nb095_alpha_dummy_152 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_155 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_156 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_152 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_157 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_148 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_149 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_158 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_151 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_152 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_159 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_160 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_151 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_161 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_162 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_152 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_152 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_163 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_133 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_164 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_135 f)
          (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_135 f)
          (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_093 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_165 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_166 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_167 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_168 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_169 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_170 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_171 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_015 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_172 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_015 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_173 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_174 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_175 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_176 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_171 f)
          (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_171 f)
          (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_177 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_178 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_179 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_172 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_180 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_172 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_181 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_177 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_177 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_182 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_179 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_179 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_179 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_183 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_184 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_185 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_187 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_188 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_189 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_184 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_190 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_187 f))
          (Class.cv (nb095_alpha_dummy_188 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_187 f)) (Class.cv (nb095_alpha_dummy_188 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_191 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_192 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_188 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_193 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_184 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_185 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_194 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_187 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_188 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_195 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_196 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_187 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_197 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_198 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_188 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_188 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_199 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_169 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_012 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_200 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_171 f)
          (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_171 f)
          (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_015 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_201 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_202 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_203 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_204 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_205 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_206 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_207 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_208 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_209 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_210 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_211 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_207 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_212 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_207 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_213 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_214 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_211 f)
            (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_215 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_216 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_211 f)
          (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_211 f)
          (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_217 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_218 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_219 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_212 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_220 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_212 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_221 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_217 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_217 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_222 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_219 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_219 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_219 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_223 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_224 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_225 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_226 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_227 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_228 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_229 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_224 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_230 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_227 f))
          (Class.cv (nb095_alpha_dummy_228 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_227 f)) (Class.cv (nb095_alpha_dummy_228 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_231 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_232 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_228 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_233 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_224 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_225 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_234 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_227 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_228 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_235 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_236 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_227 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_237 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_238 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_228 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_228 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_239 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_209 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_240 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_211 f)
          (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_211 f)
          (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_241 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_242 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_243 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_244 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_245 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cnin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_246 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
      ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_247 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_248 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar
    ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_249 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_250 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_251 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_252 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (Class.cv x))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_253 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_002 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_254 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_255 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_256 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_257 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_251 x R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_258 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_251 x R))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_259 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_260 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_261 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_262 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_257 x R)
          (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
              (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_257 x R)
          (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
              (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_263 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_264 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_265 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_258 x R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_266 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_258 x R))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_267 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_263 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_263 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_268 (x : Var) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_265 x R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_265 x R)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_265 x R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_269 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_270 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_271 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_272 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_273 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_274 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_275 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_270 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_276 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
          (Class.cv (nb095_alpha_dummy_274 x R)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_273 x R))
          (Class.cv (nb095_alpha_dummy_274 x R)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_277 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_278 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_274 x R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_279 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_270 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_271 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_280 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_273 x R)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_274 x R)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_281 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_282 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_273 x R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_283 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_284 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_274 x R))).fv ∪
      ((Class.cv (nb095_alpha_dummy_274 x R))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_285 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_255 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_249 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_286 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_257 x R)
          (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_257 x R)
          (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_251 x R))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_287 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_288 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_289 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_290 (x : Var) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_258 x R)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_291 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv ∪
      ((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_292 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv ∪
      ((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_293 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_294 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    Var :=
  (freshVar (((syn_crn (Class.cv f))).fv ∪ ((syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_295 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_296 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_297 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_298 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_299 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) 0)

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

@[expose]
noncomputable def nb095_alpha_dummy_300 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_301 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_297 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_302 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_297 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_303 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_304 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_305 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_306 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_301 f)
          (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_301 f)
          (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_307 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_308 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_309 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_302 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_310 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_302 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_311 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_307 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_307 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_312 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_309 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_309 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_309 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_313 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_314 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_315 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_316 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_317 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_318 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_319 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_314 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_320 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_317 f))
          (Class.cv (nb095_alpha_dummy_318 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_317 f)) (Class.cv (nb095_alpha_dummy_318 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_321 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_322 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_318 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_323 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_314 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_315 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_324 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_317 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_318 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_325 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_326 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_317 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_327 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_328 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_318 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_318 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_329 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_330 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_301 f)
          (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_301 f)
          (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_331 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_332 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_333 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_334 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_335 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cnin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_336 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar (((syn_cnin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
      ((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_337 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_338 (u : Var) (S_cls : Class) (E : Class) : Var :=
  (freshVar ((E).fv ∪
      ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_339 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
      ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_340 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
      ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_341 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_342 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_343 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_001 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_344 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_345 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_346 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_347 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
      ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_348 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
      ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_349 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_350 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_347 u S_cls)
            (syn_wrex (nb095_alpha_dummy_348 u S_cls) (Class.cv (nb095_alpha_dummy_342 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_341 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_351 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_352 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_347 u S_cls)
          (syn_wrex (nb095_alpha_dummy_348 u S_cls) (Class.cv (nb095_alpha_dummy_342 u S_cls))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
              (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
            (Class.cv (nb095_alpha_dummy_342 u S_cls))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
              (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_353 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_354 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_355 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_356 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_357 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_353 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_353 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_358 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_355 u S_cls)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_355 u S_cls)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_359 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_360 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_361 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_362 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_363 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_364 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_365 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_360 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_366 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
          (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_363 u S_cls))
          (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_367 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_368 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
      ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_369 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_360 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_361 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_370 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_363 u S_cls)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_364 u S_cls)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_371 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_372 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
      ((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_373 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_374 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv ∪
      ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_375 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_376 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_347 u S_cls)
          (syn_wrex (nb095_alpha_dummy_348 u S_cls) (Class.cv (nb095_alpha_dummy_341 u S_cls))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_347 u S_cls)
          (syn_wrex (nb095_alpha_dummy_348 u S_cls) (Class.cv (nb095_alpha_dummy_341 u S_cls))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_377 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_378 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_379 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_380 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_381 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))
          (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
            (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))
          (syn_cid))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_382 (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
          (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
          (syn_cid))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_383 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
          (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))))).fv ∪
      ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_384 (f : Var) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪
      ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_385 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_386 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_387 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_388 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_389 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_390 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_391 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (({(nb095_alpha_dummy_385 D R S_cls E)} : Finset Var) ∪
        ({(nb095_alpha_dummy_386 D R S_cls E)} : Finset Var) ∪
      ((syn_wex (nb095_alpha_dummy_387 D R S_cls E) (syn_wa
            (syn_wbr (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E)))
            (syn_wbr (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_392 (f : Var) : Var :=
  (freshVar (({(nb095_alpha_dummy_388 f)} : Finset Var) ∪
        ({(nb095_alpha_dummy_389 f)} : Finset Var) ∪ ((syn_wex (nb095_alpha_dummy_390 f) (syn_wa
            (syn_wbr (Class.cv (nb095_alpha_dummy_388 f))
              (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb095_alpha_dummy_390 f)))
            (syn_wbr (Class.cv (nb095_alpha_dummy_390 f)) (syn_ccnv (Class.cv f))
              (Class.cv (nb095_alpha_dummy_389 f)))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_393 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_394 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_395 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_389 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_396 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_389 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_397 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_398 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_399 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_400 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_395 f)
          (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_395 f)
          (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_401 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_402 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_403 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_396 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_404 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_396 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_405 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_401 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_401 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_406 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_403 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_403 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_403 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_407 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_408 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_409 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_410 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_411 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_412 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_413 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_408 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_414 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_411 f))
          (Class.cv (nb095_alpha_dummy_412 f)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_411 f)) (Class.cv (nb095_alpha_dummy_412 f)))).fv)
    0)

@[expose]
noncomputable def nb095_alpha_dummy_415 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_416 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_412 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_417 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_408 D R S_cls E)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_409 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_418 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb095_alpha_dummy_411 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb095_alpha_dummy_412 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_419 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_420 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_411 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_421 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_422 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_412 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_412 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_423 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_424 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_395 f)
          (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_395 f)
          (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
              (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_425 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_426 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_427 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_428 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))).fv ∪
      ((syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_429 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_430 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
      ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_431 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_390 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_432 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
      ((Class.cv (nb095_alpha_dummy_390 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_433 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_434 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_435 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
          (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
            (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
              (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_436 (f : Var) : Var :=
  (freshVar (((Class.cab (nb095_alpha_dummy_431 f)
          (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))).fv ∪
      ((Class.cab (nb095_alpha_dummy_431 f)
          (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
            (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
              (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_437 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_438 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_439 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_432 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_440 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_432 f))).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_441 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_437 D R S_cls E)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_437 D R S_cls E)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_442 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb095_alpha_dummy_439 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb095_alpha_dummy_439 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb095_alpha_dummy_439 f))).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_443 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_444 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_445 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_446 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb095_alpha_dummy_447 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb095_alpha_dummy_448 (f : Var) : Var :=
  (freshVar (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb095_alpha_dummy_449 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv ∪
      ((syn_cnin (Class.cv (nb095_alpha_dummy_444 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_445 D R S_cls E)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
