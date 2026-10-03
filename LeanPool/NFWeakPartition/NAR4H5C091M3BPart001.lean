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

@[expose]
noncomputable def nb091_alpha_dummy_000 (D : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_001 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪
      ((syn_cec (syn_chnwcutcode R D
            (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))) (syn_chwniso D))).fv)
    0)

@[expose]
noncomputable def nb091_alpha_dummy_002 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (({ p } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪
      ((syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))) (syn_chwniso D))).fv)
    0)

@[expose]
noncomputable def nb091_alpha_dummy_003 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪
        ({(nb091_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
          (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
              (syn_chwniso D))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_004 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (({ p } : Finset Var) ∪ ({(nb091_alpha_dummy_002 D R p)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
          (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
            (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
              (syn_chwniso D))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_005 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_001 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_006 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_001 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_007 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_008 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_009 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_010 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
              (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_011 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_005 D R)
          (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_005 D R)
          (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_012 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_007 D R p)
          (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
            (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_007 D R p)
          (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
            (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_013 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_006 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_014 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_006 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_015 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_016 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_017 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_013 D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_013 D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_013 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_018 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_015 D R p)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_015 D R p)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_015 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_019 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_020 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_021 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_022 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_023 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_024 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_025 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
          (Class.cv (nb091_alpha_dummy_021 D R)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
          (Class.cv (nb091_alpha_dummy_021 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_026 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
          (Class.cv (nb091_alpha_dummy_024 D R p)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
          (Class.cv (nb091_alpha_dummy_024 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_027 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_021 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_028 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_024 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_029 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_020 D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_021 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_030 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_023 D R p)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_024 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_031 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_020 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_032 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_023 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_033 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_021 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_021 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_034 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_024 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_024 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_035 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_005 D R)
          (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_005 D R)
          (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_036 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_007 D R p)
          (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv (nb091_alpha_dummy_002 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_007 D R p)
          (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv (nb091_alpha_dummy_002 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_037 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_038 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_039 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_040 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_041 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
            (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_042 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
            (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_043 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_chwniso D)).fv ∪
      ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_044 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_chwniso D)).fv ∪
      ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_045 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_chnwcutcode R D
        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_046 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_047 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
      ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_048 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
      ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_049 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_050 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_051 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_047 D R)
            (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_052 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_049 D R p)
            (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_053 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
            (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
              (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_054 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
            (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
            (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_055 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
      ((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_056 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cnin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_057 (D : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_058 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_059 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
      ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_060 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
      ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_061 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_062 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_063 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb091_alpha_dummy_059 D R)} : Finset Var) ∪
        ({(nb091_alpha_dummy_060 D R)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
          (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_064 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (({(nb091_alpha_dummy_061 D R p)} : Finset Var) ∪
        ({(nb091_alpha_dummy_062 D R p)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
          (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_065 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_060 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_066 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_060 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_067 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_068 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_069 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_070 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_067 D R p)
            (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_061 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_062 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_071 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_065 D R)
          (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_065 D R)
          (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_072 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_067 D R p)
          (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_061 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_067 D R p)
          (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_061 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_073 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_066 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_074 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_066 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_075 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_076 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_077 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_073 D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_073 D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_073 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_078 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_075 D R p)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_075 D R p)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_075 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_079 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_080 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_081 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_082 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_083 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_084 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_085 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
          (Class.cv (nb091_alpha_dummy_081 D R)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
          (Class.cv (nb091_alpha_dummy_081 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_086 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
          (Class.cv (nb091_alpha_dummy_084 D R p)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
          (Class.cv (nb091_alpha_dummy_084 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_087 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_081 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_088 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_084 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_089 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_080 D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_081 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_090 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_083 D R p)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_084 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_091 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_080 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_092 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_083 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_093 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_081 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_081 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_094 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_084 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_084 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_095 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_065 D R)
          (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_065 D R)
          (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_096 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_067 D R p)
          (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_062 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_067 D R p)
          (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_062 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_097 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_098 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_099 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_100 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_101 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
      ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_102 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cnin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_103 (D : Class) (R : Class) : Var :=
  (freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_104 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_105 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_106 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_107 (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_108 (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_109 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_110 (p : Var) : Var :=
  (freshVar (((syn_cuni (syn_cuni (Class.cv p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_111 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_112 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_113 (p : Var) : Var :=
  (freshVar (((syn_cuni (Class.cv p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_114 (p : Var) : Var :=
  (freshVar (((syn_cuni (Class.cv p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_115 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_000 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_116 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_000 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_117 (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_118 (p : Var) : Var :=
  (freshVar (((Class.cv p)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_119 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_105 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_120 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_105 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_121 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_107 R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_122 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_107 R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_123 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_124 (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_125 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_119 D R)
          (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_119 D R)
          (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_126 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_121 R p)
          (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_121 R p)
          (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_127 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_120 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_128 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_120 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_129 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_122 R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_130 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_122 R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_131 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_127 D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_127 D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_127 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_132 (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_129 R p)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_129 R p)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_129 R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_133 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_134 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_135 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_136 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_137 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_138 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_139 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
          (Class.cv (nb091_alpha_dummy_135 D R)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
          (Class.cv (nb091_alpha_dummy_135 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_140 (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
          (Class.cv (nb091_alpha_dummy_138 R p)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
          (Class.cv (nb091_alpha_dummy_138 R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_141 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_135 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_142 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_138 R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_143 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_134 D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_135 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_144 (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_137 R p)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_138 R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_145 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_134 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_146 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_137 R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_147 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_135 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_135 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_148 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_138 R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_138 R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_149 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_119 D R)
          (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_119 D R)
          (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

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
noncomputable def nb091_alpha_dummy_150 (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_121 R p)
          (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_121 R p)
          (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_151 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_152 (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_153 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_154 (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_155 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_048 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_156 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_048 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_157 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_158 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_159 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_155 D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_155 D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_155 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_160 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_157 D R p)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_157 D R p)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_157 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_161 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_162 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_163 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_164 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_165 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_166 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_167 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
          (Class.cv (nb091_alpha_dummy_163 D R)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
          (Class.cv (nb091_alpha_dummy_163 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_168 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
          (Class.cv (nb091_alpha_dummy_166 D R p)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
          (Class.cv (nb091_alpha_dummy_166 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_169 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_163 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_170 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_166 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_171 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_162 D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_163 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_172 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_165 D R p)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_166 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_173 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_162 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_174 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_165 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_175 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_163 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_163 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_176 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_166 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_166 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_177 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_047 D R)
          (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_178 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_049 D R p)
          (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_179 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_180 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_181 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_182 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_183 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_041 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_184 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_041 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_185 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_186 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_187 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_188 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb091_alpha_dummy_185 D R p)
            (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_044 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_043 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_189 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_183 D R)
          (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_183 D R)
          (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
              (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_190 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_185 D R p)
          (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_044 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))))).fv ∪
      ((Class.cab (nb091_alpha_dummy_185 D R p)
          (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_044 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
              (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_191 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_184 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_192 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_184 D R))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_193 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_194 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_195 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_191 D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_191 D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_191 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_196 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb091_alpha_dummy_193 D R p)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb091_alpha_dummy_193 D R p)) (syn_c1c))).fv ∪
      ((Class.cv (nb091_alpha_dummy_193 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_197 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_198 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_199 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_200 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_201 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb091_alpha_dummy_202 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb091_alpha_dummy_203 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
          (Class.cv (nb091_alpha_dummy_199 D R)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
          (Class.cv (nb091_alpha_dummy_199 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_204 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
          (Class.cv (nb091_alpha_dummy_202 D R p)))).fv ∪
      ((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
          (Class.cv (nb091_alpha_dummy_202 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_205 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_199 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_206 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_202 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_207 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_198 D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_199 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_208 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb091_alpha_dummy_201 D R p)))).fv ∪
      ((syn_ccompl (Class.cv (nb091_alpha_dummy_202 D R p)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_209 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_198 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_210 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_201 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_211 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_199 D R))).fv ∪
      ((Class.cv (nb091_alpha_dummy_199 D R))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_212 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cv (nb091_alpha_dummy_202 D R p))).fv ∪
      ((Class.cv (nb091_alpha_dummy_202 D R p))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_213 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_183 D R)
          (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_183 D R)
          (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_214 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((Class.cab (nb091_alpha_dummy_185 D R p)
          (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_043 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_185 D R p)
          (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_043 D R p))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
              (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_215 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_216 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_217 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))).fv) 0)

@[expose]
noncomputable def nb091_alpha_dummy_218 (D : Class) (R : Class) (p : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))).fv ∪
      ((syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))).fv) 0)

theorem nb091_fresh_000 (D : Class) (R : Class) :
    (nb091_alpha_dummy_011 D R) ∉
      (((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))))).fv)
      0

theorem nb091_fresh_001 (D : Class) (R : Class) :
    (nb091_alpha_dummy_035 D R) ∉
      (((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_002 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_036 D R p) ∉
      (((Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
              (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
              (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_003 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_012 D R p) ∉
      (((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))))).fv)
      0

theorem nb091_fresh_004 (D : Class) (R : Class) :
    (nb091_alpha_dummy_177 D R) ∉
      (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_047 D R)
            (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_177] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_047 D R)
            (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_005 (D : Class) (R : Class) :
    (nb091_alpha_dummy_053 D R) ∉
      (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
                (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
                (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_053] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
                (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
                (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv)
      0

theorem nb091_fresh_006 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_178 D R p) ∉
      (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_049 D R p)
            (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_178] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_049 D R p)
            (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_007 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_054 D R p) ∉
      (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_054] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv)
      0

theorem nb091_fresh_008 (D : Class) (R : Class) :
    (nb091_alpha_dummy_071 D R) ∉
      (((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))).fv)
      0

theorem nb091_fresh_009 (D : Class) (R : Class) :
    (nb091_alpha_dummy_095 D R) ∉
      (((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_095] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_010 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_072 D R p) ∉
      (((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_061 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_061 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_061 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_061 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))).fv)
      0

theorem nb091_fresh_011 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_096 D R p) ∉
      (((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_062 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_067 D R p)
            (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_062 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_096] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_062 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_067 D R p)
            (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_062 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_012 (D : Class) (R : Class) :
    (nb091_alpha_dummy_149 D R) ∉
      (((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_149] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_013 (D : Class) (R : Class) :
    (nb091_alpha_dummy_125 D R) ∉
      (((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_125] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))).fv)
      0

theorem nb091_fresh_014 (R : Class) (p : Var) :
    (nb091_alpha_dummy_150 R p) ∉
      (((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_150] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_015 (R : Class) (p : Var) :
    (nb091_alpha_dummy_126 R p) ∉
      (((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_126] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))).fv)
      0

theorem nb091_fresh_016 (D : Class) (R : Class) :
    (nb091_alpha_dummy_213 D R) ∉
      (((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_213] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_017 (D : Class) (R : Class) :
    (nb091_alpha_dummy_189 D R) ∉
      (((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_189] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))))).fv)
      0

theorem nb091_fresh_018 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_214 D R p) ∉
      (((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_043 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_185 D R p)
            (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_043 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_214] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_043 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_185 D R p)
            (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_043 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb091_fresh_019 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_190 D R p) ∉
      (((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_044 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_044 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_190] using
    freshVar_not_mem
      (((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_044 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_044 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))))).fv)
      0

theorem nb091_fresh_020 (D : Class) (R : Class) :
    (nb091_alpha_dummy_115 D R) ∉ (((Class.cv (nb091_alpha_dummy_000 D R))).fv) := by
  simpa only [nb091_alpha_dummy_115] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_000 D R))).fv) 0

theorem nb091_fresh_021 (D : Class) (R : Class) :
    (nb091_alpha_dummy_116 D R) ∉ (((Class.cv (nb091_alpha_dummy_000 D R))).fv) := by
  simpa only [nb091_alpha_dummy_116] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_000 D R))).fv) 1

theorem nb091_distinct_022 (D : Class) (R : Class) :
    (nb091_alpha_dummy_115 D R) ≠ (nb091_alpha_dummy_116 D R) := by
  simpa only [nb091_alpha_dummy_115, nb091_alpha_dummy_116] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_000 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_023 (D : Class) (R : Class) :
    (nb091_alpha_dummy_005 D R) ∉
      (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_001 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_001 D R))).fv)
      0

theorem nb091_fresh_024 (D : Class) (R : Class) :
    (nb091_alpha_dummy_006 D R) ∉
      (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_001 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_001 D R))).fv)
      1

theorem nb091_distinct_025 (D : Class) (R : Class) :
    (nb091_alpha_dummy_005 D R) ≠ (nb091_alpha_dummy_006 D R) := by
  simpa only [nb091_alpha_dummy_005, nb091_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_001 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_026 (D : Class) (R : Class) :
    (nb091_alpha_dummy_013 D R) ∉ (((Class.cv (nb091_alpha_dummy_006 D R))).fv) := by
  simpa only [nb091_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_006 D R))).fv) 0

theorem nb091_fresh_027 (D : Class) (R : Class) :
    (nb091_alpha_dummy_014 D R) ∉ (((Class.cv (nb091_alpha_dummy_006 D R))).fv) := by
  simpa only [nb091_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_006 D R))).fv) 1

theorem nb091_distinct_028 (D : Class) (R : Class) :
    (nb091_alpha_dummy_013 D R) ≠ (nb091_alpha_dummy_014 D R) := by
  simpa only [nb091_alpha_dummy_013, nb091_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_006 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_029 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_015 D R p) ∉ (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) := by
  simpa only [nb091_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) 0

theorem nb091_fresh_030 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_016 D R p) ∉ (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) := by
  simpa only [nb091_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) 1

theorem nb091_distinct_031 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_016 D R p) := by
  simpa only [nb091_alpha_dummy_015, nb091_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_032 (D : Class) (R : Class) :
    (nb091_alpha_dummy_019 D R) ∉
      (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_033 (D : Class) (R : Class) :
    (nb091_alpha_dummy_020 D R) ∉
      (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_034 (D : Class) (R : Class) :
    (nb091_alpha_dummy_021 D R) ∉
      (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_035 (D : Class) (R : Class) :
    (nb091_alpha_dummy_019 D R) ≠ (nb091_alpha_dummy_020 D R) := by
  simpa only [nb091_alpha_dummy_019, nb091_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_036 (D : Class) (R : Class) :
    (nb091_alpha_dummy_019 D R) ≠ (nb091_alpha_dummy_021 D R) := by
  simpa only [nb091_alpha_dummy_019, nb091_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_037 (D : Class) (R : Class) :
    (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_021 D R) := by
  simpa only [nb091_alpha_dummy_020, nb091_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_038 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_022 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_039 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_023 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_040 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_024 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_041 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_022 D R p) ≠ (nb091_alpha_dummy_023 D R p) := by
  simpa only [nb091_alpha_dummy_022, nb091_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_042 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_022 D R p) ≠ (nb091_alpha_dummy_024 D R p) := by
  simpa only [nb091_alpha_dummy_022, nb091_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_043 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_024 D R p) := by
  simpa only [nb091_alpha_dummy_023, nb091_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_044 (D : Class) (R : Class) :
    (nb091_alpha_dummy_031 D R) ∉
      (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_020 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_020 D R))).fv)
      0

theorem nb091_fresh_045 (D : Class) (R : Class) :
    (nb091_alpha_dummy_027 D R) ∉
      (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_021 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_021 D R))).fv)
      0

theorem nb091_fresh_046 (D : Class) (R : Class) :
    (nb091_alpha_dummy_033 D R) ∉
      (((Class.cv (nb091_alpha_dummy_021 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_021 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_021 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_021 D R))).fv)
      0

theorem nb091_fresh_047 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_032 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_023 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_023 D R p))).fv)
      0

theorem nb091_fresh_048 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_028 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_024 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_024 D R p))).fv)
      0

theorem nb091_fresh_049 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_034 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_024 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_024 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_024 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_024 D R p))).fv)
      0

theorem nb091_fresh_050 (D : Class) (R : Class) :
    (nb091_alpha_dummy_183 D R) ∉
      (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_041 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_183] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_041 D R))).fv)
      0

theorem nb091_fresh_051 (D : Class) (R : Class) :
    (nb091_alpha_dummy_184 D R) ∉
      (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_041 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_184] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_041 D R))).fv)
      1

theorem nb091_distinct_052 (D : Class) (R : Class) :
    (nb091_alpha_dummy_183 D R) ≠ (nb091_alpha_dummy_184 D R) := by
  simpa only [nb091_alpha_dummy_183, nb091_alpha_dummy_184] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_041 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_053 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_185 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_185] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_043 D R p))).fv)
      0

theorem nb091_fresh_054 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_186 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_186] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_043 D R p))).fv)
      1

theorem nb091_distinct_055 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_185 D R p) ≠ (nb091_alpha_dummy_186 D R p) := by
  simpa only [nb091_alpha_dummy_185, nb091_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_056 (D : Class) (R : Class) :
    (nb091_alpha_dummy_155 D R) ∉ (((Class.cv (nb091_alpha_dummy_048 D R))).fv) := by
  simpa only [nb091_alpha_dummy_155] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_048 D R))).fv) 0

theorem nb091_fresh_057 (D : Class) (R : Class) :
    (nb091_alpha_dummy_156 D R) ∉ (((Class.cv (nb091_alpha_dummy_048 D R))).fv) := by
  simpa only [nb091_alpha_dummy_156] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_048 D R))).fv) 1

theorem nb091_distinct_058 (D : Class) (R : Class) :
    (nb091_alpha_dummy_155 D R) ≠ (nb091_alpha_dummy_156 D R) := by
  simpa only [nb091_alpha_dummy_155, nb091_alpha_dummy_156] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_048 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_059 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_157 D R p) ∉ (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) := by
  simpa only [nb091_alpha_dummy_157] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) 0

theorem nb091_fresh_060 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_158 D R p) ∉ (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) := by
  simpa only [nb091_alpha_dummy_158] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) 1

theorem nb091_distinct_061 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_157 D R p) ≠ (nb091_alpha_dummy_158 D R p) := by
  simpa only [nb091_alpha_dummy_157, nb091_alpha_dummy_158] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_062 (D : Class) (R : Class) :
    (nb091_alpha_dummy_065 D R) ∉
      (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_060 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_060 D R))).fv)
      0

theorem nb091_fresh_063 (D : Class) (R : Class) :
    (nb091_alpha_dummy_066 D R) ∉
      (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_060 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_066] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_060 D R))).fv)
      1

theorem nb091_distinct_064 (D : Class) (R : Class) :
    (nb091_alpha_dummy_065 D R) ≠ (nb091_alpha_dummy_066 D R) := by
  simpa only [nb091_alpha_dummy_065, nb091_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_060 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_065 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_067 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_067] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_062 D R p))).fv)
      0

theorem nb091_fresh_066 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_068 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_062 D R p))).fv)
      1

theorem nb091_distinct_067 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_067 D R p) ≠ (nb091_alpha_dummy_068 D R p) := by
  simpa only [nb091_alpha_dummy_067, nb091_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_068 (D : Class) (R : Class) :
    (nb091_alpha_dummy_073 D R) ∉ (((Class.cv (nb091_alpha_dummy_066 D R))).fv) := by
  simpa only [nb091_alpha_dummy_073] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_066 D R))).fv) 0

theorem nb091_fresh_069 (D : Class) (R : Class) :
    (nb091_alpha_dummy_074 D R) ∉ (((Class.cv (nb091_alpha_dummy_066 D R))).fv) := by
  simpa only [nb091_alpha_dummy_074] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_066 D R))).fv) 1

theorem nb091_distinct_070 (D : Class) (R : Class) :
    (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_074 D R) := by
  simpa only [nb091_alpha_dummy_073, nb091_alpha_dummy_074] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_066 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_071 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_075 D R p) ∉ (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) := by
  simpa only [nb091_alpha_dummy_075] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) 0

theorem nb091_fresh_072 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_076 D R p) ∉ (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) := by
  simpa only [nb091_alpha_dummy_076] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) 1

theorem nb091_distinct_073 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_076 D R p) := by
  simpa only [nb091_alpha_dummy_075, nb091_alpha_dummy_076] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_074 (D : Class) (R : Class) :
    (nb091_alpha_dummy_079 D R) ∉
      (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_079] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_075 (D : Class) (R : Class) :
    (nb091_alpha_dummy_080 D R) ∉
      (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_080] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_076 (D : Class) (R : Class) :
    (nb091_alpha_dummy_081 D R) ∉
      (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_077 (D : Class) (R : Class) :
    (nb091_alpha_dummy_079 D R) ≠ (nb091_alpha_dummy_080 D R) := by
  simpa only [nb091_alpha_dummy_079, nb091_alpha_dummy_080] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv)
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
    (nb091_alpha_dummy_079 D R) ≠ (nb091_alpha_dummy_081 D R) := by
  simpa only [nb091_alpha_dummy_079, nb091_alpha_dummy_081] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_079 (D : Class) (R : Class) :
    (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_081 D R) := by
  simpa only [nb091_alpha_dummy_080, nb091_alpha_dummy_081] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_080 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_082 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_082] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_081 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_083 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_083] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_082 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_084 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_084] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_083 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_082 D R p) ≠ (nb091_alpha_dummy_083 D R p) := by
  simpa only [nb091_alpha_dummy_082, nb091_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_084 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_082 D R p) ≠ (nb091_alpha_dummy_084 D R p) := by
  simpa only [nb091_alpha_dummy_082, nb091_alpha_dummy_084] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_085 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_084 D R p) := by
  simpa only [nb091_alpha_dummy_083, nb091_alpha_dummy_084] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_086 (D : Class) (R : Class) :
    (nb091_alpha_dummy_091 D R) ∉
      (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_080 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_091] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_080 D R))).fv)
      0

theorem nb091_fresh_087 (D : Class) (R : Class) :
    (nb091_alpha_dummy_087 D R) ∉
      (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_081 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_087] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_081 D R))).fv)
      0

theorem nb091_fresh_088 (D : Class) (R : Class) :
    (nb091_alpha_dummy_093 D R) ∉
      (((Class.cv (nb091_alpha_dummy_081 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_081 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_081 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_081 D R))).fv)
      0

theorem nb091_fresh_089 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_092 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_083 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_092] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_083 D R p))).fv)
      0

theorem nb091_fresh_090 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_088 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_084 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_088] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_084 D R p))).fv)
      0

theorem nb091_fresh_091 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_094 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_084 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_084 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_084 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_084 D R p))).fv)
      0

theorem nb091_fresh_092 (D : Class) (R : Class) :
    (nb091_alpha_dummy_119 D R) ∉
      (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_105 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_105 D R))).fv)
      0

theorem nb091_fresh_093 (D : Class) (R : Class) :
    (nb091_alpha_dummy_120 D R) ∉
      (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_105 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_105 D R))).fv)
      1

theorem nb091_distinct_094 (D : Class) (R : Class) :
    (nb091_alpha_dummy_119 D R) ≠ (nb091_alpha_dummy_120 D R) := by
  simpa only [nb091_alpha_dummy_119, nb091_alpha_dummy_120] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_105 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_095 (R : Class) (p : Var) :
    (nb091_alpha_dummy_121 R p) ∉
      (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_107 R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_107 R p))).fv)
      0

theorem nb091_fresh_096 (R : Class) (p : Var) :
    (nb091_alpha_dummy_122 R p) ∉
      (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_107 R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_107 R p))).fv)
      1

theorem nb091_distinct_097 (R : Class) (p : Var) :
    (nb091_alpha_dummy_121 R p) ≠ (nb091_alpha_dummy_122 R p) := by
  simpa only [nb091_alpha_dummy_121, nb091_alpha_dummy_122] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_098 (D : Class) (R : Class) :
    (nb091_alpha_dummy_127 D R) ∉ (((Class.cv (nb091_alpha_dummy_120 D R))).fv) := by
  simpa only [nb091_alpha_dummy_127] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_120 D R))).fv) 0

theorem nb091_fresh_099 (D : Class) (R : Class) :
    (nb091_alpha_dummy_128 D R) ∉ (((Class.cv (nb091_alpha_dummy_120 D R))).fv) := by
  simpa only [nb091_alpha_dummy_128] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_120 D R))).fv) 1

theorem nb091_distinct_100 (D : Class) (R : Class) :
    (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_128 D R) := by
  simpa only [nb091_alpha_dummy_127, nb091_alpha_dummy_128] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_120 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_101 (R : Class) (p : Var) :
    (nb091_alpha_dummy_129 R p) ∉ (((Class.cv (nb091_alpha_dummy_122 R p))).fv) := by
  simpa only [nb091_alpha_dummy_129] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_122 R p))).fv) 0

theorem nb091_fresh_102 (R : Class) (p : Var) :
    (nb091_alpha_dummy_130 R p) ∉ (((Class.cv (nb091_alpha_dummy_122 R p))).fv) := by
  simpa only [nb091_alpha_dummy_130] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_122 R p))).fv) 1

theorem nb091_distinct_103 (R : Class) (p : Var) :
    (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_130 R p) := by
  simpa only [nb091_alpha_dummy_129, nb091_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_122 R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_104 (D : Class) (R : Class) :
    (nb091_alpha_dummy_133 D R) ∉
      (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_133] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_105 (D : Class) (R : Class) :
    (nb091_alpha_dummy_134 D R) ∉
      (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_134] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_106 (D : Class) (R : Class) :
    (nb091_alpha_dummy_135 D R) ∉
      (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_135] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_107 (D : Class) (R : Class) :
    (nb091_alpha_dummy_133 D R) ≠ (nb091_alpha_dummy_134 D R) := by
  simpa only [nb091_alpha_dummy_133, nb091_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_108 (D : Class) (R : Class) :
    (nb091_alpha_dummy_133 D R) ≠ (nb091_alpha_dummy_135 D R) := by
  simpa only [nb091_alpha_dummy_133, nb091_alpha_dummy_135] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_109 (D : Class) (R : Class) :
    (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_135 D R) := by
  simpa only [nb091_alpha_dummy_134, nb091_alpha_dummy_135] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_110 (R : Class) (p : Var) :
    (nb091_alpha_dummy_136 R p) ∉
      (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_136] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_111 (R : Class) (p : Var) :
    (nb091_alpha_dummy_137 R p) ∉
      (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_137] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_112 (R : Class) (p : Var) :
    (nb091_alpha_dummy_138 R p) ∉
      (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_138] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_113 (R : Class) (p : Var) :
    (nb091_alpha_dummy_136 R p) ≠ (nb091_alpha_dummy_137 R p) := by
  simpa only [nb091_alpha_dummy_136, nb091_alpha_dummy_137] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_114 (R : Class) (p : Var) :
    (nb091_alpha_dummy_136 R p) ≠ (nb091_alpha_dummy_138 R p) := by
  simpa only [nb091_alpha_dummy_136, nb091_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_115 (R : Class) (p : Var) :
    (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_138 R p) := by
  simpa only [nb091_alpha_dummy_137, nb091_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_116 (D : Class) (R : Class) :
    (nb091_alpha_dummy_145 D R) ∉
      (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_134 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_145] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_134 D R))).fv)
      0

theorem nb091_fresh_117 (D : Class) (R : Class) :
    (nb091_alpha_dummy_141 D R) ∉
      (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_135 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_141] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_135 D R))).fv)
      0

theorem nb091_fresh_118 (D : Class) (R : Class) :
    (nb091_alpha_dummy_147 D R) ∉
      (((Class.cv (nb091_alpha_dummy_135 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_135 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_147] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_135 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_135 D R))).fv)
      0

theorem nb091_fresh_119 (R : Class) (p : Var) :
    (nb091_alpha_dummy_146 R p) ∉
      (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_137 R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_146] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_137 R p))).fv)
      0

theorem nb091_fresh_120 (R : Class) (p : Var) :
    (nb091_alpha_dummy_142 R p) ∉
      (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_138 R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_142] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_138 R p))).fv)
      0

theorem nb091_fresh_121 (R : Class) (p : Var) :
    (nb091_alpha_dummy_148 R p) ∉
      (((Class.cv (nb091_alpha_dummy_138 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_138 R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_148] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_138 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_138 R p))).fv)
      0

theorem nb091_fresh_122 (D : Class) (R : Class) :
    (nb091_alpha_dummy_161 D R) ∉
      (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_161] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_123 (D : Class) (R : Class) :
    (nb091_alpha_dummy_162 D R) ∉
      (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_162] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_124 (D : Class) (R : Class) :
    (nb091_alpha_dummy_163 D R) ∉
      (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_163] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_125 (D : Class) (R : Class) :
    (nb091_alpha_dummy_161 D R) ≠ (nb091_alpha_dummy_162 D R) := by
  simpa only [nb091_alpha_dummy_161, nb091_alpha_dummy_162] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_126 (D : Class) (R : Class) :
    (nb091_alpha_dummy_161 D R) ≠ (nb091_alpha_dummy_163 D R) := by
  simpa only [nb091_alpha_dummy_161, nb091_alpha_dummy_163] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_127 (D : Class) (R : Class) :
    (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_163 D R) := by
  simpa only [nb091_alpha_dummy_162, nb091_alpha_dummy_163] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_128 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_164 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_164] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_129 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_165 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_165] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_130 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_166 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_166] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_131 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_164 D R p) ≠ (nb091_alpha_dummy_165 D R p) := by
  simpa only [nb091_alpha_dummy_164, nb091_alpha_dummy_165] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_132 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_164 D R p) ≠ (nb091_alpha_dummy_166 D R p) := by
  simpa only [nb091_alpha_dummy_164, nb091_alpha_dummy_166] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_133 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_166 D R p) := by
  simpa only [nb091_alpha_dummy_165, nb091_alpha_dummy_166] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_134 (D : Class) (R : Class) :
    (nb091_alpha_dummy_173 D R) ∉
      (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_162 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_173] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_162 D R))).fv)
      0

theorem nb091_fresh_135 (D : Class) (R : Class) :
    (nb091_alpha_dummy_169 D R) ∉
      (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_163 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_169] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_163 D R))).fv)
      0

theorem nb091_fresh_136 (D : Class) (R : Class) :
    (nb091_alpha_dummy_175 D R) ∉
      (((Class.cv (nb091_alpha_dummy_163 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_163 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_175] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_163 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_163 D R))).fv)
      0

theorem nb091_fresh_137 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_174 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_165 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_174] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_165 D R p))).fv)
      0

theorem nb091_fresh_138 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_170 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_166 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_170] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_166 D R p))).fv)
      0

theorem nb091_fresh_139 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_176 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_166 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_166 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_176] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_166 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_166 D R p))).fv)
      0

theorem nb091_fresh_140 (D : Class) (R : Class) :
    (nb091_alpha_dummy_191 D R) ∉ (((Class.cv (nb091_alpha_dummy_184 D R))).fv) := by
  simpa only [nb091_alpha_dummy_191] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_184 D R))).fv) 0

theorem nb091_fresh_141 (D : Class) (R : Class) :
    (nb091_alpha_dummy_192 D R) ∉ (((Class.cv (nb091_alpha_dummy_184 D R))).fv) := by
  simpa only [nb091_alpha_dummy_192] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_184 D R))).fv) 1

theorem nb091_distinct_142 (D : Class) (R : Class) :
    (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_192 D R) := by
  simpa only [nb091_alpha_dummy_191, nb091_alpha_dummy_192] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_184 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_143 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_193 D R p) ∉ (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) := by
  simpa only [nb091_alpha_dummy_193] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) 0

theorem nb091_fresh_144 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_194 D R p) ∉ (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) := by
  simpa only [nb091_alpha_dummy_194] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) 1

theorem nb091_distinct_145 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_194 D R p) := by
  simpa only [nb091_alpha_dummy_193, nb091_alpha_dummy_194] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb091_fresh_146 (D : Class) (R : Class) :
    (nb091_alpha_dummy_197 D R) ∉
      (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_197] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_147 (D : Class) (R : Class) :
    (nb091_alpha_dummy_198 D R) ∉
      (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_198] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_148 (D : Class) (R : Class) :
    (nb091_alpha_dummy_199 D R) ∉
      (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_199] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_149 (D : Class) (R : Class) :
    (nb091_alpha_dummy_197 D R) ≠ (nb091_alpha_dummy_198 D R) := by
  simpa only [nb091_alpha_dummy_197, nb091_alpha_dummy_198] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_150 (D : Class) (R : Class) :
    (nb091_alpha_dummy_197 D R) ≠ (nb091_alpha_dummy_199 D R) := by
  simpa only [nb091_alpha_dummy_197, nb091_alpha_dummy_199] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_151 (D : Class) (R : Class) :
    (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_199 D R) := by
  simpa only [nb091_alpha_dummy_198, nb091_alpha_dummy_199] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_152 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_200 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_200] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) 0

theorem nb091_fresh_153 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_201 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_201] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) 1

theorem nb091_fresh_154 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_202 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb091_alpha_dummy_202] using
    freshVar_not_mem (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) 2

theorem nb091_distinct_155 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_200 D R p) ≠ (nb091_alpha_dummy_201 D R p) := by
  simpa only [nb091_alpha_dummy_200, nb091_alpha_dummy_201] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_distinct_156 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_200 D R p) ≠ (nb091_alpha_dummy_202 D R p) := by
  simpa only [nb091_alpha_dummy_200, nb091_alpha_dummy_202] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb091_distinct_157 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_202 D R p) := by
  simpa only [nb091_alpha_dummy_201, nb091_alpha_dummy_202] using
    (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb091_fresh_158 (D : Class) (R : Class) :
    (nb091_alpha_dummy_209 D R) ∉
      (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_198 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_209] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_198 D R))).fv)
      0

theorem nb091_fresh_159 (D : Class) (R : Class) :
    (nb091_alpha_dummy_205 D R) ∉
      (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_199 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_205] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_199 D R))).fv)
      0

theorem nb091_fresh_160 (D : Class) (R : Class) :
    (nb091_alpha_dummy_211 D R) ∉
      (((Class.cv (nb091_alpha_dummy_199 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_199 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_211] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_199 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_199 D R))).fv)
      0

theorem nb091_fresh_161 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_210 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_201 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_210] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_201 D R p))).fv)
      0

theorem nb091_fresh_162 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_206 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_202 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_206] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_202 D R p))).fv)
      0

theorem nb091_fresh_163 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_212 D R p) ∉
      (((Class.cv (nb091_alpha_dummy_202 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_202 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_212] using
    freshVar_not_mem
      (((Class.cv (nb091_alpha_dummy_202 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_202 D R p))).fv)
      0

theorem nb091_fresh_164 (p : Var) : (nb091_alpha_dummy_117 p) ∉ (((Class.cv p)).fv) := by
  simpa only [nb091_alpha_dummy_117] using freshVar_not_mem (((Class.cv p)).fv) 0

theorem nb091_fresh_165 (p : Var) : (nb091_alpha_dummy_118 p) ∉ (((Class.cv p)).fv) := by
  simpa only [nb091_alpha_dummy_118] using freshVar_not_mem (((Class.cv p)).fv) 1

theorem nb091_distinct_166 (p : Var) :
    (nb091_alpha_dummy_117 p) ≠ (nb091_alpha_dummy_118 p) := by
  simpa only [nb091_alpha_dummy_117, nb091_alpha_dummy_118] using
    (freshVar_injective (((Class.cv p)).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_167 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_007 D R p) ∉
      (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) 0

theorem nb091_fresh_168 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_008 D R p) ∉
      (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) 1

theorem nb091_distinct_169 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_007 D R p) ≠ (nb091_alpha_dummy_008 D R p) := by
  simpa only [nb091_alpha_dummy_007, nb091_alpha_dummy_008] using
    (freshVar_injective
      (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb091_fresh_170 (D : Class) (R : Class) :
    (nb091_alpha_dummy_017 D R) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_013 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_013 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_013 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_013 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_013 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_013 D R))).fv)
      0

theorem nb091_fresh_171 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_018 D R p) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_015 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_015 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_015 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_015 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_015 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_015 D R p))).fv)
      0

theorem nb091_fresh_172 (D : Class) (R : Class) :
    (nb091_alpha_dummy_077 D R) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_073 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_073 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_073 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_077] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_073 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_073 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_073 D R))).fv)
      0

theorem nb091_fresh_173 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_078 D R p) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_075 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_075 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_075 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_078] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_075 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_075 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_075 D R p))).fv)
      0

theorem nb091_fresh_174 (D : Class) (R : Class) :
    (nb091_alpha_dummy_131 D R) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_127 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_127 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_127 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_131] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_127 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_127 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_127 D R))).fv)
      0

theorem nb091_fresh_175 (R : Class) (p : Var) :
    (nb091_alpha_dummy_132 R p) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_129 R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_129 R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_129 R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_132] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_129 R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_129 R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_129 R p))).fv)
      0

theorem nb091_fresh_176 (D : Class) (R : Class) :
    (nb091_alpha_dummy_159 D R) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_155 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_155 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_155 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_159] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_155 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_155 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_155 D R))).fv)
      0

theorem nb091_fresh_177 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_160 D R p) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_157 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_157 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_157 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_160] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_157 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_157 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_157 D R p))).fv)
      0

theorem nb091_fresh_178 (D : Class) (R : Class) :
    (nb091_alpha_dummy_195 D R) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_191 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_191 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_191 D R))).fv) :=
  by
  simpa only [nb091_alpha_dummy_195] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_191 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_191 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_191 D R))).fv)
      0

theorem nb091_fresh_179 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_196 D R p) ∉
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_193 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_193 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_193 D R p))).fv) :=
  by
  simpa only [nb091_alpha_dummy_196] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_193 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_193 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_193 D R p))).fv)
      0

theorem nb091_fresh_180 (D : Class) (R : Class) :
    (nb091_alpha_dummy_105 D R) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_105] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv)
      0

theorem nb091_fresh_181 (D : Class) (R : Class) :
    (nb091_alpha_dummy_106 D R) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_106] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv)
      1

theorem nb091_distinct_182 (D : Class) (R : Class) :
    (nb091_alpha_dummy_105 D R) ≠ (nb091_alpha_dummy_106 D R) := by
  simpa only [nb091_alpha_dummy_105, nb091_alpha_dummy_106] using
    (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_183 (R : Class) (p : Var) :
    (nb091_alpha_dummy_107 R p) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_107] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv)
      0

theorem nb091_fresh_184 (R : Class) (p : Var) :
    (nb091_alpha_dummy_108 R p) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_108] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv)
      1

theorem nb091_distinct_185 (R : Class) (p : Var) :
    (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_108 R p) := by
  simpa only [nb091_alpha_dummy_107, nb091_alpha_dummy_108] using
    (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_186 (D : Class) (R : Class) :
    (nb091_alpha_dummy_009 D R) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_187 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_010 D R p) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_007 D R p)
              (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
                (Class.cv (nb091_alpha_dummy_002 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_007 D R p)
              (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
                (Class.cv (nb091_alpha_dummy_002 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_188 (D : Class) (R : Class) :
    (nb091_alpha_dummy_051 D R) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                            (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_051] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                            (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_189 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_052 D R p) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_049 D R p)
              (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_049 D R p)
              (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_190 (D : Class) (R : Class) :
    (nb091_alpha_dummy_069 D R) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_069] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_191 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_070 D R p) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_067 D R p)
              (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_061 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
                (Class.cv (nb091_alpha_dummy_062 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_070] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_067 D R p)
              (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_061 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
                (Class.cv (nb091_alpha_dummy_062 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_192 (D : Class) (R : Class) :
    (nb091_alpha_dummy_123 D R) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_123] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_193 (R : Class) (p : Var) :
    (nb091_alpha_dummy_124 R p) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_124] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_194 (D : Class) (R : Class) :
    (nb091_alpha_dummy_187 D R) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_187] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_195 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_188 D R p) ∉
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_185 D R p)
              (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_044 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
                (Class.cv (nb091_alpha_dummy_043 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_188] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_185 D R p)
              (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_044 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
                (Class.cv (nb091_alpha_dummy_043 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb091_fresh_196 (D : Class) (R : Class) :
    (nb091_alpha_dummy_029 D R) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_020 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_021 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_020 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_021 D R)))).fv)
      0

theorem nb091_fresh_197 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_030 D R p) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_023 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_024 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_023 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_024 D R p)))).fv)
      0

theorem nb091_fresh_198 (D : Class) (R : Class) :
    (nb091_alpha_dummy_089 D R) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_080 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_081 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_089] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_080 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_081 D R)))).fv)
      0

theorem nb091_fresh_199 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_090 D R p) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_083 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_084 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_090] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_083 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_084 D R p)))).fv)
      0

theorem nb091_fresh_200 (D : Class) (R : Class) :
    (nb091_alpha_dummy_143 D R) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_134 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_135 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_143] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_134 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_135 D R)))).fv)
      0

theorem nb091_fresh_201 (R : Class) (p : Var) :
    (nb091_alpha_dummy_144 R p) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_137 R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_138 R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_144] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_137 R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_138 R p)))).fv)
      0

theorem nb091_fresh_202 (D : Class) (R : Class) :
    (nb091_alpha_dummy_171 D R) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_162 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_163 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_171] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_162 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_163 D R)))).fv)
      0

theorem nb091_fresh_203 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_172 D R p) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_165 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_166 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_172] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_165 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_166 D R p)))).fv)
      0

theorem nb091_fresh_204 (D : Class) (R : Class) :
    (nb091_alpha_dummy_207 D R) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_198 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_199 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_207] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_198 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_199 D R)))).fv)
      0

theorem nb091_fresh_205 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_208 D R p) ∉
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_201 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_202 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_208] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_201 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_202 D R p)))).fv)
      0

theorem nb091_fresh_206 (D : Class) (R : Class) :
    (nb091_alpha_dummy_037 D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_207 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_038 D R p) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_208 (D : Class) (R : Class) :
    (nb091_alpha_dummy_179 D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_179] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_209 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_180 D R p) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_180] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_210 (D : Class) (R : Class) :
    (nb091_alpha_dummy_097 D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_097] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_211 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_098 D R p) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_098] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_212 (D : Class) (R : Class) :
    (nb091_alpha_dummy_151 D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_213 (R : Class) (p : Var) :
    (nb091_alpha_dummy_152 R p) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_214 (D : Class) (R : Class) :
    (nb091_alpha_dummy_215 D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_215] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_215 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_216 D R p) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_216] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb091_fresh_216 (D : Class) (R : Class) :
    (nb091_alpha_dummy_045 D R) ∉
      (((syn_chnwcutcode R D
          (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_045] using
    freshVar_not_mem
      (((syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv)
      0

theorem nb091_fresh_217 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_046 D R p) ∉
      (((syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_046] using
    freshVar_not_mem (((syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))).fv) 0

theorem nb091_fresh_218 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∉
      (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
              (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
              (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
      0

theorem nb091_fresh_219 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∉
      (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
              (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
              (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
      1

theorem nb091_distinct_220 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_042 D R) := by
  simpa only [nb091_alpha_dummy_041, nb091_alpha_dummy_042] using
    (freshVar_injective (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
              (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_221 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∉
      (((syn_chwniso D)).fv ∪
        ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_chwniso D)).fv ∪
        ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv)
      0

theorem nb091_fresh_222 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∉
      (((syn_chwniso D)).fv ∪
        ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_chwniso D)).fv ∪
        ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv)
      1

theorem nb091_distinct_223 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_044 D R p) := by
  simpa only [nb091_alpha_dummy_043, nb091_alpha_dummy_044] using
    (freshVar_injective (((syn_chwniso D)).fv ∪
        ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_224 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_059] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
