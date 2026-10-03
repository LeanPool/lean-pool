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

@[expose]
noncomputable def nb096_alpha_dummy_000 (D : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (D).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_001 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪
      ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_002 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (({ q } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_003 (D : Class) (R : Class) : Var :=
  (freshVar (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪
        ({(nb096_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
          (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_004 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (({ q } : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
          (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_005 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_001 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_006 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_001 D R))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_007 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_008 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_009 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_010 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
              (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_011 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_005 D R)
          (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
              (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))))).fv ∪
      ((Class.cab (nb096_alpha_dummy_005 D R)
          (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
              (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_012 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_007 D R q)
          (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
            (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
              (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))))).fv ∪
      ((Class.cab (nb096_alpha_dummy_007 D R q)
          (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
            (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
              (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_013 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_006 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_014 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_006 D R))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_015 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_016 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_017 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096_alpha_dummy_013 D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb096_alpha_dummy_013 D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb096_alpha_dummy_013 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_018 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096_alpha_dummy_015 D R q)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb096_alpha_dummy_015 D R q)) (syn_c1c))).fv ∪
      ((Class.cv (nb096_alpha_dummy_015 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_019 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_020 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_021 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb096_alpha_dummy_022 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_023 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_024 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb096_alpha_dummy_025 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
          (Class.cv (nb096_alpha_dummy_021 D R)))).fv ∪
      ((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
          (Class.cv (nb096_alpha_dummy_021 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_026 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
          (Class.cv (nb096_alpha_dummy_024 D R q)))).fv ∪
      ((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
          (Class.cv (nb096_alpha_dummy_024 D R q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_027 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_021 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_028 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_024 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_029 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb096_alpha_dummy_020 D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb096_alpha_dummy_021 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_030 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb096_alpha_dummy_023 D R q)))).fv ∪
      ((syn_ccompl (Class.cv (nb096_alpha_dummy_024 D R q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_031 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_020 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_032 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_023 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_033 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_021 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_021 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_034 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_024 D R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_024 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_035 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_005 D R)
          (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_005 D R)
          (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_036 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_007 D R q)
          (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv (nb096_alpha_dummy_002 D R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_007 D R q)
          (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv (nb096_alpha_dummy_002 D R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_037 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_038 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_039 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))).fv ∪
      ((syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_040 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))).fv ∪
      ((syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_041 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_042 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_043 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_044 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_045 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_046 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_047 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv ∪
      ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_048 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv ∪ ((syn_cnin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_049 (D : Class) (R : Class) : Var :=
  (freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_050 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_051 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_052 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_053 (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_054 (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
      ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_055 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_056 (q : Var) : Var :=
  (freshVar (((syn_cuni (syn_cuni (Class.cv q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_057 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_058 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_059 (q : Var) : Var :=
  (freshVar (((syn_cuni (Class.cv q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_060 (q : Var) : Var :=
  (freshVar (((syn_cuni (Class.cv q))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_061 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_000 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_062 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_000 D R))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_063 (q : Var) : Var :=
  (freshVar (((Class.cv q)).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_064 (q : Var) : Var :=
  (freshVar (((Class.cv q)).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_065 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_051 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_066 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_051 D R))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_067 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_053 R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_068 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_053 R q))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_069 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_070 (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_071 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_065 D R)
          (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
              (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))).fv ∪
      ((Class.cab (nb096_alpha_dummy_065 D R)
          (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
              (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_072 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_067 R q)
          (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
              (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))).fv ∪
      ((Class.cab (nb096_alpha_dummy_067 R q)
          (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
              (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_073 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_066 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_074 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_066 D R))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_075 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_068 R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_076 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_068 R q))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_077 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096_alpha_dummy_073 D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb096_alpha_dummy_073 D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb096_alpha_dummy_073 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_078 (R : Class) (q : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096_alpha_dummy_075 R q)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb096_alpha_dummy_075 R q)) (syn_c1c))).fv ∪
      ((Class.cv (nb096_alpha_dummy_075 R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_079 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_080 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_081 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb096_alpha_dummy_082 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_083 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_084 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb096_alpha_dummy_085 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
          (Class.cv (nb096_alpha_dummy_081 D R)))).fv ∪
      ((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
          (Class.cv (nb096_alpha_dummy_081 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_086 (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
          (Class.cv (nb096_alpha_dummy_084 R q)))).fv ∪
      ((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
          (Class.cv (nb096_alpha_dummy_084 R q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_087 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_081 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_088 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_084 R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_089 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb096_alpha_dummy_080 D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb096_alpha_dummy_081 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_090 (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb096_alpha_dummy_083 R q)))).fv ∪
      ((syn_ccompl (Class.cv (nb096_alpha_dummy_084 R q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_091 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_080 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_092 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_083 R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_093 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_081 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_081 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_094 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_084 R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_084 R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_095 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_065 D R)
          (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_065 D R)
          (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_096 (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_067 R q)
          (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_067 R q)
          (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_097 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_098 (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_099 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))).fv ∪
      ((syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_100 (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))).fv ∪
      ((syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_101 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_041 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_102 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_041 D R))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_103 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_104 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_105 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_106 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb096_alpha_dummy_103 D R q)
            (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_044 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_043 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_107 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_101 D R)
          (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
              (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))))).fv ∪
      ((Class.cab (nb096_alpha_dummy_101 D R)
          (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
              (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_108 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_103 D R q)
          (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_044 D R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
              (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))))).fv ∪
      ((Class.cab (nb096_alpha_dummy_103 D R q)
          (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_044 D R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
              (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_109 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_102 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_110 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_102 D R))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_111 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_112 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_113 (D : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096_alpha_dummy_109 D R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb096_alpha_dummy_109 D R)) (syn_c1c))).fv ∪
      ((Class.cv (nb096_alpha_dummy_109 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_114 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb096_alpha_dummy_111 D R q)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb096_alpha_dummy_111 D R q)) (syn_c1c))).fv ∪
      ((Class.cv (nb096_alpha_dummy_111 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_115 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_116 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_117 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb096_alpha_dummy_118 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_119 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb096_alpha_dummy_120 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb096_alpha_dummy_121 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
          (Class.cv (nb096_alpha_dummy_117 D R)))).fv ∪
      ((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
          (Class.cv (nb096_alpha_dummy_117 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_122 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
          (Class.cv (nb096_alpha_dummy_120 D R q)))).fv ∪
      ((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
          (Class.cv (nb096_alpha_dummy_120 D R q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_123 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_117 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_124 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_120 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_125 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb096_alpha_dummy_116 D R)))).fv ∪
      ((syn_ccompl (Class.cv (nb096_alpha_dummy_117 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_126 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb096_alpha_dummy_119 D R q)))).fv ∪
      ((syn_ccompl (Class.cv (nb096_alpha_dummy_120 D R q)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_127 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_116 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_128 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_119 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_129 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_117 D R))).fv ∪
      ((Class.cv (nb096_alpha_dummy_117 D R))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_130 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cv (nb096_alpha_dummy_120 D R q))).fv ∪
      ((Class.cv (nb096_alpha_dummy_120 D R q))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_131 (D : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_101 D R)
          (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_101 D R)
          (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_132 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((Class.cab (nb096_alpha_dummy_103 D R q)
          (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_043 D R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_103 D R q)
          (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_043 D R q))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
              (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_133 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_134 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_135 (D : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv ∪
      ((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv) 0)

@[expose]
noncomputable def nb096_alpha_dummy_136 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv ∪
      ((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv) 0)

theorem nb096_fresh_000 (D : Class) (R : Class) :
    (nb096_alpha_dummy_011 D R) ∉
      (((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))))).fv)
      0

theorem nb096_fresh_001 (D : Class) (R : Class) :
    (nb096_alpha_dummy_035 D R) ∉
      (((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb096_fresh_002 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_036 D R q) ∉
      (((Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
              (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
              (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb096_fresh_003 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_012 D R q) ∉
      (((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))))).fv)
      0

theorem nb096_fresh_004 (D : Class) (R : Class) :
    (nb096_alpha_dummy_095 D R) ∉
      (((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_095] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb096_fresh_005 (D : Class) (R : Class) :
    (nb096_alpha_dummy_071 D R) ∉
      (((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))).fv)
      0

theorem nb096_fresh_006 (R : Class) (q : Var) :
    (nb096_alpha_dummy_096 R q) ∉
      (((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_096] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb096_fresh_007 (R : Class) (q : Var) :
    (nb096_alpha_dummy_072 R q) ∉
      (((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))).fv)
      0

theorem nb096_fresh_008 (D : Class) (R : Class) :
    (nb096_alpha_dummy_131 D R) ∉
      (((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_131] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb096_fresh_009 (D : Class) (R : Class) :
    (nb096_alpha_dummy_107 D R) ∉
      (((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_107] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))))).fv)
      0

theorem nb096_fresh_010 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_132 D R q) ∉
      (((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_043 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_103 D R q)
            (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_043 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_132] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_043 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_103 D R q)
            (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_043 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb096_fresh_011 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_108 D R q) ∉
      (((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_044 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_044 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_108] using
    freshVar_not_mem
      (((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_044 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_044 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))))).fv)
      0

theorem nb096_fresh_012 (D : Class) (R : Class) :
    (nb096_alpha_dummy_061 D R) ∉ (((Class.cv (nb096_alpha_dummy_000 D R))).fv) := by
  simpa only [nb096_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_000 D R))).fv) 0

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
    (nb096_alpha_dummy_062 D R) ∉ (((Class.cv (nb096_alpha_dummy_000 D R))).fv) := by
  simpa only [nb096_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_000 D R))).fv) 1

theorem nb096_distinct_014 (D : Class) (R : Class) :
    (nb096_alpha_dummy_061 D R) ≠ (nb096_alpha_dummy_062 D R) := by
  simpa only [nb096_alpha_dummy_061, nb096_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_000 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_015 (D : Class) (R : Class) :
    (nb096_alpha_dummy_005 D R) ∉
      (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_001 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_001 D R))).fv)
      0

theorem nb096_fresh_016 (D : Class) (R : Class) :
    (nb096_alpha_dummy_006 D R) ∉
      (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_001 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_001 D R))).fv)
      1

theorem nb096_distinct_017 (D : Class) (R : Class) :
    (nb096_alpha_dummy_005 D R) ≠ (nb096_alpha_dummy_006 D R) := by
  simpa only [nb096_alpha_dummy_005, nb096_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_018 (D : Class) (R : Class) :
    (nb096_alpha_dummy_013 D R) ∉ (((Class.cv (nb096_alpha_dummy_006 D R))).fv) := by
  simpa only [nb096_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_006 D R))).fv) 0

theorem nb096_fresh_019 (D : Class) (R : Class) :
    (nb096_alpha_dummy_014 D R) ∉ (((Class.cv (nb096_alpha_dummy_006 D R))).fv) := by
  simpa only [nb096_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_006 D R))).fv) 1

theorem nb096_distinct_020 (D : Class) (R : Class) :
    (nb096_alpha_dummy_013 D R) ≠ (nb096_alpha_dummy_014 D R) := by
  simpa only [nb096_alpha_dummy_013, nb096_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_021 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_015 D R q) ∉ (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) := by
  simpa only [nb096_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) 0

theorem nb096_fresh_022 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_016 D R q) ∉ (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) := by
  simpa only [nb096_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) 1

theorem nb096_distinct_023 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_016 D R q) := by
  simpa only [nb096_alpha_dummy_015, nb096_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_024 (D : Class) (R : Class) :
    (nb096_alpha_dummy_019 D R) ∉
      (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb096_fresh_025 (D : Class) (R : Class) :
    (nb096_alpha_dummy_020 D R) ∉
      (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb096_fresh_026 (D : Class) (R : Class) :
    (nb096_alpha_dummy_021 D R) ∉
      (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb096_distinct_027 (D : Class) (R : Class) :
    (nb096_alpha_dummy_019 D R) ≠ (nb096_alpha_dummy_020 D R) := by
  simpa only [nb096_alpha_dummy_019, nb096_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_028 (D : Class) (R : Class) :
    (nb096_alpha_dummy_019 D R) ≠ (nb096_alpha_dummy_021 D R) := by
  simpa only [nb096_alpha_dummy_019, nb096_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_029 (D : Class) (R : Class) :
    (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_021 D R) := by
  simpa only [nb096_alpha_dummy_020, nb096_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_030 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_022 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) 0

theorem nb096_fresh_031 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_023 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) 1

theorem nb096_fresh_032 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_024 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) 2

theorem nb096_distinct_033 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_022 D R q) ≠ (nb096_alpha_dummy_023 D R q) := by
  simpa only [nb096_alpha_dummy_022, nb096_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_034 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_022 D R q) ≠ (nb096_alpha_dummy_024 D R q) := by
  simpa only [nb096_alpha_dummy_022, nb096_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_035 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_024 D R q) := by
  simpa only [nb096_alpha_dummy_023, nb096_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_036 (D : Class) (R : Class) :
    (nb096_alpha_dummy_031 D R) ∉
      (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_020 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_020 D R))).fv)
      0

theorem nb096_fresh_037 (D : Class) (R : Class) :
    (nb096_alpha_dummy_027 D R) ∉
      (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_021 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_021 D R))).fv)
      0

theorem nb096_fresh_038 (D : Class) (R : Class) :
    (nb096_alpha_dummy_033 D R) ∉
      (((Class.cv (nb096_alpha_dummy_021 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_021 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_021 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_021 D R))).fv)
      0

theorem nb096_fresh_039 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_032 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_023 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_023 D R q))).fv)
      0

theorem nb096_fresh_040 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_028 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_024 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_024 D R q))).fv)
      0

theorem nb096_fresh_041 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_034 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_024 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_024 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_024 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_024 D R q))).fv)
      0

theorem nb096_fresh_042 (D : Class) (R : Class) :
    (nb096_alpha_dummy_101 D R) ∉
      (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_041 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_101] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_041 D R))).fv)
      0

theorem nb096_fresh_043 (D : Class) (R : Class) :
    (nb096_alpha_dummy_102 D R) ∉
      (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_041 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_102] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_041 D R))).fv)
      1

theorem nb096_distinct_044 (D : Class) (R : Class) :
    (nb096_alpha_dummy_101 D R) ≠ (nb096_alpha_dummy_102 D R) := by
  simpa only [nb096_alpha_dummy_101, nb096_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_041 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_045 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_103 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_103] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_043 D R q))).fv)
      0

theorem nb096_fresh_046 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_104 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_104] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_043 D R q))).fv)
      1

theorem nb096_distinct_047 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_103 D R q) ≠ (nb096_alpha_dummy_104 D R q) := by
  simpa only [nb096_alpha_dummy_103, nb096_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_048 (D : Class) (R : Class) :
    (nb096_alpha_dummy_065 D R) ∉
      (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv)
      0

theorem nb096_fresh_049 (D : Class) (R : Class) :
    (nb096_alpha_dummy_066 D R) ∉
      (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_066] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv)
      1

theorem nb096_distinct_050 (D : Class) (R : Class) :
    (nb096_alpha_dummy_065 D R) ≠ (nb096_alpha_dummy_066 D R) := by
  simpa only [nb096_alpha_dummy_065, nb096_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_051 (R : Class) (q : Var) :
    (nb096_alpha_dummy_067 R q) ∉
      (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_053 R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_067] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_053 R q))).fv)
      0

theorem nb096_fresh_052 (R : Class) (q : Var) :
    (nb096_alpha_dummy_068 R q) ∉
      (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_053 R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_053 R q))).fv)
      1

theorem nb096_distinct_053 (R : Class) (q : Var) :
    (nb096_alpha_dummy_067 R q) ≠ (nb096_alpha_dummy_068 R q) := by
  simpa only [nb096_alpha_dummy_067, nb096_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_053 R q))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_054 (D : Class) (R : Class) :
    (nb096_alpha_dummy_073 D R) ∉ (((Class.cv (nb096_alpha_dummy_066 D R))).fv) := by
  simpa only [nb096_alpha_dummy_073] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_066 D R))).fv) 0

theorem nb096_fresh_055 (D : Class) (R : Class) :
    (nb096_alpha_dummy_074 D R) ∉ (((Class.cv (nb096_alpha_dummy_066 D R))).fv) := by
  simpa only [nb096_alpha_dummy_074] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_066 D R))).fv) 1

theorem nb096_distinct_056 (D : Class) (R : Class) :
    (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_074 D R) := by
  simpa only [nb096_alpha_dummy_073, nb096_alpha_dummy_074] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_066 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_057 (R : Class) (q : Var) :
    (nb096_alpha_dummy_075 R q) ∉ (((Class.cv (nb096_alpha_dummy_068 R q))).fv) := by
  simpa only [nb096_alpha_dummy_075] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_068 R q))).fv) 0

theorem nb096_fresh_058 (R : Class) (q : Var) :
    (nb096_alpha_dummy_076 R q) ∉ (((Class.cv (nb096_alpha_dummy_068 R q))).fv) := by
  simpa only [nb096_alpha_dummy_076] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_068 R q))).fv) 1

theorem nb096_distinct_059 (R : Class) (q : Var) :
    (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_076 R q) := by
  simpa only [nb096_alpha_dummy_075, nb096_alpha_dummy_076] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_068 R q))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_060 (D : Class) (R : Class) :
    (nb096_alpha_dummy_079 D R) ∉
      (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_079] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb096_fresh_061 (D : Class) (R : Class) :
    (nb096_alpha_dummy_080 D R) ∉
      (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_080] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb096_fresh_062 (D : Class) (R : Class) :
    (nb096_alpha_dummy_081 D R) ∉
      (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb096_distinct_063 (D : Class) (R : Class) :
    (nb096_alpha_dummy_079 D R) ≠ (nb096_alpha_dummy_080 D R) := by
  simpa only [nb096_alpha_dummy_079, nb096_alpha_dummy_080] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_064 (D : Class) (R : Class) :
    (nb096_alpha_dummy_079 D R) ≠ (nb096_alpha_dummy_081 D R) := by
  simpa only [nb096_alpha_dummy_079, nb096_alpha_dummy_081] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_065 (D : Class) (R : Class) :
    (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_081 D R) := by
  simpa only [nb096_alpha_dummy_080, nb096_alpha_dummy_081] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_066 (R : Class) (q : Var) :
    (nb096_alpha_dummy_082 R q) ∉
      (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_082] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) 0

theorem nb096_fresh_067 (R : Class) (q : Var) :
    (nb096_alpha_dummy_083 R q) ∉
      (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_083] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) 1

theorem nb096_fresh_068 (R : Class) (q : Var) :
    (nb096_alpha_dummy_084 R q) ∉
      (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_084] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) 2

theorem nb096_distinct_069 (R : Class) (q : Var) :
    (nb096_alpha_dummy_082 R q) ≠ (nb096_alpha_dummy_083 R q) := by
  simpa only [nb096_alpha_dummy_082, nb096_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_070 (R : Class) (q : Var) :
    (nb096_alpha_dummy_082 R q) ≠ (nb096_alpha_dummy_084 R q) := by
  simpa only [nb096_alpha_dummy_082, nb096_alpha_dummy_084] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_071 (R : Class) (q : Var) :
    (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_084 R q) := by
  simpa only [nb096_alpha_dummy_083, nb096_alpha_dummy_084] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_072 (D : Class) (R : Class) :
    (nb096_alpha_dummy_091 D R) ∉
      (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_080 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_091] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_080 D R))).fv)
      0

theorem nb096_fresh_073 (D : Class) (R : Class) :
    (nb096_alpha_dummy_087 D R) ∉
      (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_081 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_087] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_081 D R))).fv)
      0

theorem nb096_fresh_074 (D : Class) (R : Class) :
    (nb096_alpha_dummy_093 D R) ∉
      (((Class.cv (nb096_alpha_dummy_081 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_081 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_081 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_081 D R))).fv)
      0

theorem nb096_fresh_075 (R : Class) (q : Var) :
    (nb096_alpha_dummy_092 R q) ∉
      (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_083 R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_092] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_083 R q))).fv)
      0

theorem nb096_fresh_076 (R : Class) (q : Var) :
    (nb096_alpha_dummy_088 R q) ∉
      (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_084 R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_088] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_084 R q))).fv)
      0

theorem nb096_fresh_077 (R : Class) (q : Var) :
    (nb096_alpha_dummy_094 R q) ∉
      (((Class.cv (nb096_alpha_dummy_084 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_084 R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_084 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_084 R q))).fv)
      0

theorem nb096_fresh_078 (D : Class) (R : Class) :
    (nb096_alpha_dummy_109 D R) ∉ (((Class.cv (nb096_alpha_dummy_102 D R))).fv) := by
  simpa only [nb096_alpha_dummy_109] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_102 D R))).fv) 0

theorem nb096_fresh_079 (D : Class) (R : Class) :
    (nb096_alpha_dummy_110 D R) ∉ (((Class.cv (nb096_alpha_dummy_102 D R))).fv) := by
  simpa only [nb096_alpha_dummy_110] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_102 D R))).fv) 1

theorem nb096_distinct_080 (D : Class) (R : Class) :
    (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_110 D R) := by
  simpa only [nb096_alpha_dummy_109, nb096_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_102 D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_081 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_111 D R q) ∉ (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) := by
  simpa only [nb096_alpha_dummy_111] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) 0

theorem nb096_fresh_082 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_112 D R q) ∉ (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) := by
  simpa only [nb096_alpha_dummy_112] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) 1

theorem nb096_distinct_083 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_112 D R q) := by
  simpa only [nb096_alpha_dummy_111, nb096_alpha_dummy_112] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb096_fresh_084 (D : Class) (R : Class) :
    (nb096_alpha_dummy_115 D R) ∉
      (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_115] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb096_fresh_085 (D : Class) (R : Class) :
    (nb096_alpha_dummy_116 D R) ∉
      (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_116] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb096_fresh_086 (D : Class) (R : Class) :
    (nb096_alpha_dummy_117 D R) ∉
      (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_117] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb096_distinct_087 (D : Class) (R : Class) :
    (nb096_alpha_dummy_115 D R) ≠ (nb096_alpha_dummy_116 D R) := by
  simpa only [nb096_alpha_dummy_115, nb096_alpha_dummy_116] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_088 (D : Class) (R : Class) :
    (nb096_alpha_dummy_115 D R) ≠ (nb096_alpha_dummy_117 D R) := by
  simpa only [nb096_alpha_dummy_115, nb096_alpha_dummy_117] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_089 (D : Class) (R : Class) :
    (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_117 D R) := by
  simpa only [nb096_alpha_dummy_116, nb096_alpha_dummy_117] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_090 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_118 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_118] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) 0

theorem nb096_fresh_091 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_119 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_119] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) 1

theorem nb096_fresh_092 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_120 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb096_alpha_dummy_120] using
    freshVar_not_mem (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) 2

theorem nb096_distinct_093 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_118 D R q) ≠ (nb096_alpha_dummy_119 D R q) := by
  simpa only [nb096_alpha_dummy_118, nb096_alpha_dummy_119] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_distinct_094 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_118 D R q) ≠ (nb096_alpha_dummy_120 D R q) := by
  simpa only [nb096_alpha_dummy_118, nb096_alpha_dummy_120] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb096_distinct_095 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_120 D R q) := by
  simpa only [nb096_alpha_dummy_119, nb096_alpha_dummy_120] using
    (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb096_fresh_096 (D : Class) (R : Class) :
    (nb096_alpha_dummy_127 D R) ∉
      (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_116 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_127] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_116 D R))).fv)
      0

theorem nb096_fresh_097 (D : Class) (R : Class) :
    (nb096_alpha_dummy_123 D R) ∉
      (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_117 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_123] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_117 D R))).fv)
      0

theorem nb096_fresh_098 (D : Class) (R : Class) :
    (nb096_alpha_dummy_129 D R) ∉
      (((Class.cv (nb096_alpha_dummy_117 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_117 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_129] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_117 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_117 D R))).fv)
      0

theorem nb096_fresh_099 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_128 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_119 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_128] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_119 D R q))).fv)
      0

theorem nb096_fresh_100 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_124 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_120 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_124] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_120 D R q))).fv)
      0

theorem nb096_fresh_101 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_130 D R q) ∉
      (((Class.cv (nb096_alpha_dummy_120 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_120 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_130] using
    freshVar_not_mem
      (((Class.cv (nb096_alpha_dummy_120 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_120 D R q))).fv)
      0

theorem nb096_fresh_102 (q : Var) : (nb096_alpha_dummy_063 q) ∉ (((Class.cv q)).fv) := by
  simpa only [nb096_alpha_dummy_063] using freshVar_not_mem (((Class.cv q)).fv) 0

theorem nb096_fresh_103 (q : Var) : (nb096_alpha_dummy_064 q) ∉ (((Class.cv q)).fv) := by
  simpa only [nb096_alpha_dummy_064] using freshVar_not_mem (((Class.cv q)).fv) 1

theorem nb096_distinct_104 (q : Var) :
    (nb096_alpha_dummy_063 q) ≠ (nb096_alpha_dummy_064 q) := by
  simpa only [nb096_alpha_dummy_063, nb096_alpha_dummy_064] using
    (freshVar_injective (((Class.cv q)).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_105 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_007 D R q) ∉
      (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) 0

theorem nb096_fresh_106 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_008 D R q) ∉
      (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) 1

theorem nb096_distinct_107 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_007 D R q) ≠ (nb096_alpha_dummy_008 D R q) := by
  simpa only [nb096_alpha_dummy_007, nb096_alpha_dummy_008] using
    (freshVar_injective
      (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb096_fresh_108 (D : Class) (R : Class) :
    (nb096_alpha_dummy_017 D R) ∉
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_013 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_013 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_013 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_013 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_013 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_013 D R))).fv)
      0

theorem nb096_fresh_109 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_018 D R q) ∉
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_015 D R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_015 D R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_015 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_015 D R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_015 D R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_015 D R q))).fv)
      0

theorem nb096_fresh_110 (D : Class) (R : Class) :
    (nb096_alpha_dummy_077 D R) ∉
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_073 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_073 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_073 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_077] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_073 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_073 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_073 D R))).fv)
      0

theorem nb096_fresh_111 (R : Class) (q : Var) :
    (nb096_alpha_dummy_078 R q) ∉
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_075 R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_075 R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_075 R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_078] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_075 R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_075 R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_075 R q))).fv)
      0

theorem nb096_fresh_112 (D : Class) (R : Class) :
    (nb096_alpha_dummy_113 D R) ∉
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_109 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_109 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_109 D R))).fv) :=
  by
  simpa only [nb096_alpha_dummy_113] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_109 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_109 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_109 D R))).fv)
      0

theorem nb096_fresh_113 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_114 D R q) ∉
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_111 D R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_111 D R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_111 D R q))).fv) :=
  by
  simpa only [nb096_alpha_dummy_114] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_111 D R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_111 D R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_111 D R q))).fv)
      0

theorem nb096_fresh_114 (D : Class) (R : Class) :
    (nb096_alpha_dummy_051 D R) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_051] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv)
      0

theorem nb096_fresh_115 (D : Class) (R : Class) :
    (nb096_alpha_dummy_052 D R) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv)
      1

theorem nb096_distinct_116 (D : Class) (R : Class) :
    (nb096_alpha_dummy_051 D R) ≠ (nb096_alpha_dummy_052 D R) := by
  simpa only [nb096_alpha_dummy_051, nb096_alpha_dummy_052] using
    (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_fresh_117 (R : Class) (q : Var) :
    (nb096_alpha_dummy_053 R q) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_053] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv)
      0

theorem nb096_fresh_118 (R : Class) (q : Var) :
    (nb096_alpha_dummy_054 R q) ∉
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_054] using
    freshVar_not_mem
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv)
      1

theorem nb096_distinct_119 (R : Class) (q : Var) :
    (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_054 R q) := by
  simpa only [nb096_alpha_dummy_053, nb096_alpha_dummy_054] using
    (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_120 (D : Class) (R : Class) :
    (nb096_alpha_dummy_009 D R) ∉
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb096_fresh_121 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_010 D R q) ∉
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_007 D R q)
              (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
                (Class.cv (nb096_alpha_dummy_002 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_007 D R q)
              (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
                (Class.cv (nb096_alpha_dummy_002 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb096_fresh_122 (D : Class) (R : Class) :
    (nb096_alpha_dummy_069 D R) ∉
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_069] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb096_fresh_123 (R : Class) (q : Var) :
    (nb096_alpha_dummy_070 R q) ∉
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_070] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb096_fresh_124 (D : Class) (R : Class) :
    (nb096_alpha_dummy_105 D R) ∉
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_105] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb096_fresh_125 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_106 D R q) ∉
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_103 D R q)
              (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_044 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
                (Class.cv (nb096_alpha_dummy_043 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_106] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_103 D R q)
              (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_044 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
                (Class.cv (nb096_alpha_dummy_043 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb096_fresh_126 (D : Class) (R : Class) :
    (nb096_alpha_dummy_029 D R) ∉
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_020 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_021 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_020 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_021 D R)))).fv)
      0

theorem nb096_fresh_127 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_030 D R q) ∉
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_023 D R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_024 D R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_023 D R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_024 D R q)))).fv)
      0

theorem nb096_fresh_128 (D : Class) (R : Class) :
    (nb096_alpha_dummy_089 D R) ∉
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_080 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_081 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_089] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_080 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_081 D R)))).fv)
      0

theorem nb096_fresh_129 (R : Class) (q : Var) :
    (nb096_alpha_dummy_090 R q) ∉
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_083 R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_084 R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_090] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_083 R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_084 R q)))).fv)
      0

theorem nb096_fresh_130 (D : Class) (R : Class) :
    (nb096_alpha_dummy_125 D R) ∉
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_116 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_117 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_125] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_116 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_117 D R)))).fv)
      0

theorem nb096_fresh_131 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_126 D R q) ∉
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_119 D R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_120 D R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_126] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_119 D R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_120 D R q)))).fv)
      0

theorem nb096_fresh_132 (D : Class) (R : Class) :
    (nb096_alpha_dummy_037 D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb096_fresh_133 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_038 D R q) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb096_fresh_134 (D : Class) (R : Class) :
    (nb096_alpha_dummy_097 D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_097] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb096_fresh_135 (R : Class) (q : Var) :
    (nb096_alpha_dummy_098 R q) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_098] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb096_fresh_136 (D : Class) (R : Class) :
    (nb096_alpha_dummy_133 D R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_133] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb096_fresh_137 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_134 D R q) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_134] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb096_fresh_138 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
      0

theorem nb096_fresh_139 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
      1

theorem nb096_distinct_140 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_042 D R) := by
  simpa only [nb096_alpha_dummy_041, nb096_alpha_dummy_042] using
    (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_fresh_141 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
      0

theorem nb096_fresh_142 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
      1

theorem nb096_distinct_143 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_044 D R q) := by
  simpa only [nb096_alpha_dummy_043, nb096_alpha_dummy_044] using
    (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb096_fresh_144 (D : Class) (R : Class) :
    (nb096_alpha_dummy_045 D R) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
              (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_045] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv)
      0

theorem nb096_fresh_145 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_046 D R q) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv)
      0

theorem nb096_fresh_146 (D : Class) (R : Class) :
    (nb096_alpha_dummy_025 D R) ∉
      (((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
            (Class.cv (nb096_alpha_dummy_021 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
            (Class.cv (nb096_alpha_dummy_021 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
            (Class.cv (nb096_alpha_dummy_021 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
            (Class.cv (nb096_alpha_dummy_021 D R)))).fv)
      0

theorem nb096_fresh_147 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_026 D R q) ∉
      (((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
            (Class.cv (nb096_alpha_dummy_024 D R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
            (Class.cv (nb096_alpha_dummy_024 D R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
            (Class.cv (nb096_alpha_dummy_024 D R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
            (Class.cv (nb096_alpha_dummy_024 D R q)))).fv)
      0

theorem nb096_fresh_148 (D : Class) (R : Class) :
    (nb096_alpha_dummy_085 D R) ∉
      (((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
            (Class.cv (nb096_alpha_dummy_081 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
            (Class.cv (nb096_alpha_dummy_081 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_085] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
            (Class.cv (nb096_alpha_dummy_081 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
            (Class.cv (nb096_alpha_dummy_081 D R)))).fv)
      0

theorem nb096_fresh_149 (R : Class) (q : Var) :
    (nb096_alpha_dummy_086 R q) ∉
      (((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
            (Class.cv (nb096_alpha_dummy_084 R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
            (Class.cv (nb096_alpha_dummy_084 R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_086] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
            (Class.cv (nb096_alpha_dummy_084 R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
            (Class.cv (nb096_alpha_dummy_084 R q)))).fv)
      0

theorem nb096_fresh_150 (D : Class) (R : Class) :
    (nb096_alpha_dummy_121 D R) ∉
      (((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
            (Class.cv (nb096_alpha_dummy_117 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
            (Class.cv (nb096_alpha_dummy_117 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_121] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
            (Class.cv (nb096_alpha_dummy_117 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
            (Class.cv (nb096_alpha_dummy_117 D R)))).fv)
      0

theorem nb096_fresh_151 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_122 D R q) ∉
      (((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
            (Class.cv (nb096_alpha_dummy_120 D R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
            (Class.cv (nb096_alpha_dummy_120 D R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_122] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
            (Class.cv (nb096_alpha_dummy_120 D R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
            (Class.cv (nb096_alpha_dummy_120 D R q)))).fv)
      0

theorem nb096_fresh_152 (D : Class) (R : Class) :
    (nb096_alpha_dummy_047 D R) ∉
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv)
      0

theorem nb096_fresh_153 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_048 D R q) ∉
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv)
      0

theorem nb096_fresh_154 (D : Class) (R : Class) :
    (nb096_alpha_dummy_039 D R) ∉
      (((syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))).fv)
      0

theorem nb096_fresh_155 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_040 D R q) ∉
      (((syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))).fv)
      0

theorem nb096_fresh_156 (D : Class) (R : Class) :
    (nb096_alpha_dummy_099 D R) ∉
      (((syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_099] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))).fv)
      0

theorem nb096_fresh_157 (R : Class) (q : Var) :
    (nb096_alpha_dummy_100 R q) ∉
      (((syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_100] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))).fv)
      0

theorem nb096_fresh_158 (D : Class) (R : Class) :
    (nb096_alpha_dummy_135 D R) ∉
      (((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_135] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv)
      0

theorem nb096_fresh_159 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_136 D R q) ∉
      (((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_136] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv)
      0

theorem nb096_fresh_160 (D : Class) (R : Class) :
    (nb096_alpha_dummy_057 D R) ∉
      (((syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_057] using
    freshVar_not_mem (((syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))).fv) 0

theorem nb096_fresh_161 (D : Class) (R : Class) :
    (nb096_alpha_dummy_058 D R) ∉
      (((syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))).fv) :=
  by
  simpa only [nb096_alpha_dummy_058] using
    freshVar_not_mem (((syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))).fv) 1

theorem nb096_distinct_162 (D : Class) (R : Class) :
    (nb096_alpha_dummy_057 D R) ≠ (nb096_alpha_dummy_058 D R) := by
  simpa only [nb096_alpha_dummy_057, nb096_alpha_dummy_058] using
    (freshVar_injective (((syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))).fv) (i := 0)
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
    (nb096_alpha_dummy_059 q) ∉ (((syn_cuni (Class.cv q))).fv) := by
  simpa only [nb096_alpha_dummy_059] using
    freshVar_not_mem (((syn_cuni (Class.cv q))).fv) 0

theorem nb096_fresh_164 (q : Var) :
    (nb096_alpha_dummy_060 q) ∉ (((syn_cuni (Class.cv q))).fv) := by
  simpa only [nb096_alpha_dummy_060] using
    freshVar_not_mem (((syn_cuni (Class.cv q))).fv) 1

theorem nb096_distinct_165 (q : Var) :
    (nb096_alpha_dummy_059 q) ≠ (nb096_alpha_dummy_060 q) := by
  simpa only [nb096_alpha_dummy_059, nb096_alpha_dummy_060] using
    (freshVar_injective (((syn_cuni (Class.cv q))).fv) (i := 0) (j := 1) (by decide))

theorem nb096_fresh_166 (D : Class) (R : Class) :
    (nb096_alpha_dummy_055 D R) ∉
      (((syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_055] using
    freshVar_not_mem (((syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))).fv) 0

theorem nb096_fresh_167 (q : Var) :
    (nb096_alpha_dummy_056 q) ∉ (((syn_cuni (syn_cuni (Class.cv q)))).fv) := by
  simpa only [nb096_alpha_dummy_056] using
    freshVar_not_mem (((syn_cuni (syn_cuni (Class.cv q)))).fv) 0

theorem nb096_fresh_168 (D : Class) (R : Class) :
    (nb096_alpha_dummy_049 D R) ∉
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
              (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_049] using
    freshVar_not_mem
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).fv)
      0

theorem nb096_fresh_169 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_050 D R q) ∉
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_050] using
    freshVar_not_mem
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).fv)
      0

theorem nb096_fresh_170 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∉ ((R).fv ∪ (D).fv) := by
  simpa only [nb096_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (D).fv) 0

theorem nb096_fresh_171 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∉
      (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_001] using
    freshVar_not_mem
      (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
      0

theorem nb096_fresh_172 (D : Class) (R : Class) :
    (nb096_alpha_dummy_003 D R) ∉
      (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪
          ({(nb096_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪
          ({(nb096_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))))).fv)
      0

theorem nb096_fresh_173 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∉
      (({ q } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_002] using
    freshVar_not_mem
      (({ q } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
      0

theorem nb096_fresh_174 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_004 D R q) ∉
      (({ q } : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv) :=
  by
  simpa only [nb096_alpha_dummy_004] using
    freshVar_not_mem
      (({ q } : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv)
      0

theorem nb096_support_mem_0000 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈
      (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪
          ({(nb096_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0001 (D : Class) (R : Class) (q : Var) :
    q ∈
      (({ q } : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0002 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∈
      (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪
          ({(nb096_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0003 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∈
      (({ q } : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0004 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈
      (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0005 (D : Class) (R : Class) (q : Var) :
    q ∈
      (({ q } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0006 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈
      (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_001 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0007 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_000 D R) ≠ (nb096_alpha_dummy_005 D R) from (by
          unfold nb096_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_000 D R) ≠ (nb096_alpha_dummy_006 D R) from (by
            unfold nb096_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0008 (D : Class) (R : Class) (q : Var) :
    q ∈ (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0009 (D : Class) (R : Class) (q : Var) :
    q ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_007 D R q)
              (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
                (Class.cv (nb096_alpha_dummy_002 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show q ≠ (nb096_alpha_dummy_007 D R q) from (by
          unfold nb096_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show q ≠ (nb096_alpha_dummy_008 D R q) from (by
            unfold nb096_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0010 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈
      (((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_000 D R) ≠ (nb096_alpha_dummy_005 D R) from (by
          unfold nb096_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_000 D R) ≠ (nb096_alpha_dummy_006 D R) from (by
            unfold nb096_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0011 (D : Class) (R : Class) (q : Var) :
    q ∈
      (((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show q ≠ (nb096_alpha_dummy_007 D R q) from (by
          unfold nb096_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show q ≠ (nb096_alpha_dummy_008 D R q) from (by
            unfold nb096_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0012 (D : Class) (R : Class) :
    (nb096_alpha_dummy_006 D R) ∈ (((Class.cv (nb096_alpha_dummy_006 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0013 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_008 D R q) ∈ (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0014 (D : Class) (R : Class) :
    (nb096_alpha_dummy_013 D R) ∈
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_013 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_013 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_013 D R))).fv) :=
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
    (nb096_alpha_dummy_015 D R q) ∈
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_015 D R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_015 D R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_015 D R q))).fv) :=
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
    (nb096_alpha_dummy_013 D R) ∈
      (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0017 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_015 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0018 (D : Class) (R : Class) :
    (nb096_alpha_dummy_020 D R) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
            (Class.cv (nb096_alpha_dummy_021 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
            (Class.cv (nb096_alpha_dummy_021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0019 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_023 D R q) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
            (Class.cv (nb096_alpha_dummy_024 D R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
            (Class.cv (nb096_alpha_dummy_024 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0020 (D : Class) (R : Class) :
    (nb096_alpha_dummy_020 D R) ∈
      (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0021 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_023 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_024 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0022 (D : Class) (R : Class) :
    (nb096_alpha_dummy_021 D R) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
            (Class.cv (nb096_alpha_dummy_021 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_020 D R))
            (Class.cv (nb096_alpha_dummy_021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0023 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_024 D R q) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
            (Class.cv (nb096_alpha_dummy_024 D R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_023 D R q))
            (Class.cv (nb096_alpha_dummy_024 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0024 (D : Class) (R : Class) :
    (nb096_alpha_dummy_021 D R) ∈
      (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0025 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_024 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_024 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0026 (D : Class) (R : Class) :
    (nb096_alpha_dummy_020 D R) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_020 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0027 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_023 D R q) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_023 D R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_024 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0028 (D : Class) (R : Class) :
    (nb096_alpha_dummy_020 D R) ∈
      (((Class.cv (nb096_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_020 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0029 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_023 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_023 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_023 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0030 (D : Class) (R : Class) :
    (nb096_alpha_dummy_021 D R) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_020 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0031 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_024 D R q) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_023 D R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_024 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0032 (D : Class) (R : Class) :
    (nb096_alpha_dummy_021 D R) ∈
      (((Class.cv (nb096_alpha_dummy_021 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0033 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_024 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_024 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_024 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0034 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∈
      (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_001 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0035 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_000 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_005 D R) from (by
          unfold nb096_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_006 D R) from (by
            unfold nb096_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0036 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∈
      (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0037 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_007 D R q)
              (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv q)
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
                (Class.cv (nb096_alpha_dummy_002 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_007 D R q) from (by
          unfold nb096_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_008 D R q) from (by
            unfold nb096_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0038 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∈
      (((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_005 D R) from (by
          unfold nb096_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_006 D R) from (by
            unfold nb096_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0039 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∈
      (((Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
              (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_007 D R q)
            (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_007 D R q) from (by
          unfold nb096_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_008 D R q) from (by
            unfold nb096_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0040 (D : Class) (R : Class) :
    (nb096_alpha_dummy_006 D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0041 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_008 D R q) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0042 (D : Class) (R : Class) :
    (nb096_alpha_dummy_006 D R) ∈
      (((syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0043 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_008 D R q) ∈
      (((syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0044 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) :=
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
      (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) :=
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
    (nb096_alpha_dummy_000 D R) ∈
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
              (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) :=
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
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) :=
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
    (nb096_alpha_dummy_000 D R) ∈
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) :=
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
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) :=
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
    (nb096_alpha_dummy_000 D R) ∈
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
              (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).fv) :=
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
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).fv) :=
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
    (nb096_alpha_dummy_000 D R) ∈
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv) :=
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
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0054 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈
      (((syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0055 (q : Var) :
    q ∈ (((syn_cuni (syn_cuni (Class.cv q)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0056 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈
      (((syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0057 (q : Var) : q ∈ (((syn_cuni (Class.cv q))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0058 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∈ (((Class.cv (nb096_alpha_dummy_000 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0059 (q : Var) : q ∈ (((Class.cv q)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0060 (D : Class) (R : Class) :
    (nb096_alpha_dummy_052 D R) ∈
      (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0061 (D : Class) (R : Class) :
    (nb096_alpha_dummy_052 D R) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_065 D R) from (by
          unfold nb096_alpha_dummy_065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_066 D R) from (by
            unfold nb096_alpha_dummy_066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0062 (R : Class) (q : Var) :
    (nb096_alpha_dummy_054 R q) ∈
      (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_053 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0063 (R : Class) (q : Var) :
    (nb096_alpha_dummy_054 R q) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
          unfold nb096_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
            unfold nb096_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0064 (D : Class) (R : Class) :
    (nb096_alpha_dummy_052 D R) ∈
      (((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_065 D R) from (by
          unfold nb096_alpha_dummy_065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_066 D R) from (by
            unfold nb096_alpha_dummy_066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0065 (R : Class) (q : Var) :
    (nb096_alpha_dummy_054 R q) ∈
      (((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
          unfold nb096_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
            unfold nb096_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0066 (D : Class) (R : Class) :
    (nb096_alpha_dummy_066 D R) ∈ (((Class.cv (nb096_alpha_dummy_066 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0067 (R : Class) (q : Var) :
    (nb096_alpha_dummy_068 R q) ∈ (((Class.cv (nb096_alpha_dummy_068 R q))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0068 (D : Class) (R : Class) :
    (nb096_alpha_dummy_073 D R) ∈
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_073 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_073 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_073 D R))).fv) :=
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
    (nb096_alpha_dummy_075 R q) ∈
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_075 R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_075 R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_075 R q))).fv) :=
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
    (nb096_alpha_dummy_073 D R) ∈
      (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0071 (R : Class) (q : Var) :
    (nb096_alpha_dummy_075 R q) ∈
      (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0072 (D : Class) (R : Class) :
    (nb096_alpha_dummy_080 D R) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
            (Class.cv (nb096_alpha_dummy_081 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
            (Class.cv (nb096_alpha_dummy_081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0073 (R : Class) (q : Var) :
    (nb096_alpha_dummy_083 R q) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
            (Class.cv (nb096_alpha_dummy_084 R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
            (Class.cv (nb096_alpha_dummy_084 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0074 (D : Class) (R : Class) :
    (nb096_alpha_dummy_080 D R) ∈
      (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0075 (R : Class) (q : Var) :
    (nb096_alpha_dummy_083 R q) ∈
      (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_084 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0076 (D : Class) (R : Class) :
    (nb096_alpha_dummy_081 D R) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
            (Class.cv (nb096_alpha_dummy_081 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_080 D R))
            (Class.cv (nb096_alpha_dummy_081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0077 (R : Class) (q : Var) :
    (nb096_alpha_dummy_084 R q) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
            (Class.cv (nb096_alpha_dummy_084 R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_083 R q))
            (Class.cv (nb096_alpha_dummy_084 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0078 (D : Class) (R : Class) :
    (nb096_alpha_dummy_081 D R) ∈
      (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0079 (R : Class) (q : Var) :
    (nb096_alpha_dummy_084 R q) ∈
      (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_084 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0080 (D : Class) (R : Class) :
    (nb096_alpha_dummy_080 D R) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_080 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0081 (R : Class) (q : Var) :
    (nb096_alpha_dummy_083 R q) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_083 R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_084 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0082 (D : Class) (R : Class) :
    (nb096_alpha_dummy_080 D R) ∈
      (((Class.cv (nb096_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_080 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0083 (R : Class) (q : Var) :
    (nb096_alpha_dummy_083 R q) ∈
      (((Class.cv (nb096_alpha_dummy_083 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_083 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0084 (D : Class) (R : Class) :
    (nb096_alpha_dummy_081 D R) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_080 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0085 (R : Class) (q : Var) :
    (nb096_alpha_dummy_084 R q) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_083 R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_084 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0086 (D : Class) (R : Class) :
    (nb096_alpha_dummy_081 D R) ∈
      (((Class.cv (nb096_alpha_dummy_081 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0087 (R : Class) (q : Var) :
    (nb096_alpha_dummy_084 R q) ∈
      (((Class.cv (nb096_alpha_dummy_084 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_084 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0088 (D : Class) (R : Class) :
    (nb096_alpha_dummy_051 D R) ∈
      (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0089 (D : Class) (R : Class) :
    (nb096_alpha_dummy_051 D R) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_051 D R) ≠ (nb096_alpha_dummy_065 D R) from (by
          unfold nb096_alpha_dummy_065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0088 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_051 D R) ≠ (nb096_alpha_dummy_066 D R) from (by
            unfold nb096_alpha_dummy_066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0088 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0090 (R : Class) (q : Var) :
    (nb096_alpha_dummy_053 R q) ∈
      (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_053 R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0091 (R : Class) (q : Var) :
    (nb096_alpha_dummy_053 R q) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
          unfold nb096_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0090 R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
            unfold nb096_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0090 R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0092 (D : Class) (R : Class) :
    (nb096_alpha_dummy_051 D R) ∈
      (((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_051 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_051 D R) ≠ (nb096_alpha_dummy_065 D R) from (by
          unfold nb096_alpha_dummy_065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0088 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_051 D R) ≠ (nb096_alpha_dummy_066 D R) from (by
            unfold nb096_alpha_dummy_066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0088 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0093 (R : Class) (q : Var) :
    (nb096_alpha_dummy_053 R q) ∈
      (((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_053 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
          unfold nb096_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0090 R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
            unfold nb096_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0090 R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0094 (D : Class) (R : Class) :
    (nb096_alpha_dummy_066 D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0095 (R : Class) (q : Var) :
    (nb096_alpha_dummy_068 R q) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0096 (D : Class) (R : Class) :
    (nb096_alpha_dummy_066 D R) ∈
      (((syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0097 (R : Class) (q : Var) :
    (nb096_alpha_dummy_068 R q) ∈
      (((syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0098 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∈
      (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_041 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0099 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_101 D R) from (by
          unfold nb096_alpha_dummy_101;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0098 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_102 D R) from (by
            unfold nb096_alpha_dummy_102;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0098 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0100 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0101 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_103 D R q)
              (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_044 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
                (Class.cv (nb096_alpha_dummy_043 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_044 D R q) ≠ (nb096_alpha_dummy_103 D R q) from (by
          unfold nb096_alpha_dummy_103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0100 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_044 D R q) ≠ (nb096_alpha_dummy_104 D R q) from (by
            unfold nb096_alpha_dummy_104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0100 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0102 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∈
      (((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_101 D R) from (by
          unfold nb096_alpha_dummy_101;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0098 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_102 D R) from (by
            unfold nb096_alpha_dummy_102;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0098 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0103 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∈
      (((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_044 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))))).fv ∪
        ((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_044 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_044 D R q) ≠ (nb096_alpha_dummy_103 D R q) from (by
          unfold nb096_alpha_dummy_103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0100 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_044 D R q) ≠ (nb096_alpha_dummy_104 D R q) from (by
            unfold nb096_alpha_dummy_104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0100 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0104 (D : Class) (R : Class) :
    (nb096_alpha_dummy_102 D R) ∈ (((Class.cv (nb096_alpha_dummy_102 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0105 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_104 D R q) ∈ (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0106 (D : Class) (R : Class) :
    (nb096_alpha_dummy_109 D R) ∈
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_109 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_109 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_109 D R))).fv) :=
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
    (nb096_alpha_dummy_111 D R q) ∈
      (((Wff.classMem (Class.cv (nb096_alpha_dummy_111 D R q)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb096_alpha_dummy_111 D R q)) (syn_c1c))).fv ∪
        ((Class.cv (nb096_alpha_dummy_111 D R q))).fv) :=
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
    (nb096_alpha_dummy_109 D R) ∈
      (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0109 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_111 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0110 (D : Class) (R : Class) :
    (nb096_alpha_dummy_116 D R) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
            (Class.cv (nb096_alpha_dummy_117 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
            (Class.cv (nb096_alpha_dummy_117 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0111 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_119 D R q) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
            (Class.cv (nb096_alpha_dummy_120 D R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
            (Class.cv (nb096_alpha_dummy_120 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0112 (D : Class) (R : Class) :
    (nb096_alpha_dummy_116 D R) ∈
      (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_117 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0113 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_119 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_120 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0114 (D : Class) (R : Class) :
    (nb096_alpha_dummy_117 D R) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
            (Class.cv (nb096_alpha_dummy_117 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_116 D R))
            (Class.cv (nb096_alpha_dummy_117 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0115 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_120 D R q) ∈
      (((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
            (Class.cv (nb096_alpha_dummy_120 D R q)))).fv ∪
        ((syn_cnin (Class.cv (nb096_alpha_dummy_119 D R q))
            (Class.cv (nb096_alpha_dummy_120 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0116 (D : Class) (R : Class) :
    (nb096_alpha_dummy_117 D R) ∈
      (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_117 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0117 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_120 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_120 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0118 (D : Class) (R : Class) :
    (nb096_alpha_dummy_116 D R) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_116 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_117 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0119 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_119 D R q) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_119 D R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_120 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0120 (D : Class) (R : Class) :
    (nb096_alpha_dummy_116 D R) ∈
      (((Class.cv (nb096_alpha_dummy_116 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_116 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0121 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_119 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_119 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_119 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0122 (D : Class) (R : Class) :
    (nb096_alpha_dummy_117 D R) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_116 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_117 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0123 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_120 D R q) ∈
      (((syn_ccompl (Class.cv (nb096_alpha_dummy_119 D R q)))).fv ∪
        ((syn_ccompl (Class.cv (nb096_alpha_dummy_120 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
