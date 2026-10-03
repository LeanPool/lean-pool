/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4H5C093M3Part001. -/


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
noncomputable def nb093_alpha_dummy_000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_002 (A : Class) : Var :=
  (freshVar (((syn_cnin (syn_clntpc A)
          (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr
              (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv ∪
      ((syn_cnin (syn_clntpc A) (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A)
            (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_003 (A : Class) (r : Var) (d : Var) : Var :=
  (freshVar (((syn_cnin (syn_clntpc A) (syn_copab r d
            (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
              (Class.cv d))))).fv ∪ ((syn_cnin (syn_clntpc A) (syn_copab r d
            (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
              (Class.cv d))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_004 (A : Class) : Var :=
  (freshVar (((syn_clntpc A)).fv ∪
      ((syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr
            (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
              (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
            (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_005 (A : Class) (r : Var) (d : Var) : Var :=
  (freshVar (((syn_clntpc A)).fv ∪ ((syn_copab r d
          (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
            (Class.cv d)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_006 (A : Class) : Var :=
  (freshVar (({(nb093_alpha_dummy_001 A)} : Finset Var) ∪
        ({(nb093_alpha_dummy_000 A)} : Finset Var) ∪ ((syn_wbr
          (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
          (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_007 (r : Var) (d : Var) : Var :=
  (freshVar (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
      ((syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound) (Class.cv d))).fv)
    0)

@[expose]
noncomputable def nb093_alpha_dummy_008 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_000 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_009 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_000 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_010 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv d)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_011 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((Class.cv d)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_012 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_013 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_014 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_008 A)
          (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
              (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))))).fv ∪
      ((Class.cab (nb093_alpha_dummy_008 A)
          (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
              (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_015 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_010 r d)
          (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
            (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
              (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))))).fv ∪
      ((Class.cab (nb093_alpha_dummy_010 r d) (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
            (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
              (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_016 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_009 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_017 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_009 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_018 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_011 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_019 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_011 r d))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_020 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093_alpha_dummy_016 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb093_alpha_dummy_016 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb093_alpha_dummy_016 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_021 (r : Var) (d : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093_alpha_dummy_018 r d)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb093_alpha_dummy_018 r d)) (syn_c1c))).fv ∪
      ((Class.cv (nb093_alpha_dummy_018 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_022 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_023 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_024 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb093_alpha_dummy_025 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_026 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_027 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb093_alpha_dummy_028 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
          (Class.cv (nb093_alpha_dummy_024 A)))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_023 A)) (Class.cv (nb093_alpha_dummy_024 A)))).fv)
    0)

@[expose]
noncomputable def nb093_alpha_dummy_029 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
          (Class.cv (nb093_alpha_dummy_027 r d)))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
          (Class.cv (nb093_alpha_dummy_027 r d)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_030 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_024 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_031 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
      ((Class.cv (nb093_alpha_dummy_027 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_032 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb093_alpha_dummy_023 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb093_alpha_dummy_024 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_033 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb093_alpha_dummy_026 r d)))).fv ∪
      ((syn_ccompl (Class.cv (nb093_alpha_dummy_027 r d)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_034 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_023 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_035 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
      ((Class.cv (nb093_alpha_dummy_026 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_036 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_024 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_024 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_037 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_027 r d))).fv ∪
      ((Class.cv (nb093_alpha_dummy_027 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_038 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_008 A)
          (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_008 A)
          (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_039 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_010 r d)
          (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
            (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_010 r d)
          (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
            (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_040 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_041 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_042 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))).fv ∪
      ((syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_043 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))).fv ∪
      ((syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_044 (A : Class) : Var :=
  (freshVar (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
          (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
      ((Class.cv (nb093_alpha_dummy_000 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_045 (A : Class) : Var :=
  (freshVar (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
          (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
      ((Class.cv (nb093_alpha_dummy_000 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_046 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_047 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_048 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb093_alpha_dummy_044 A)
            (syn_wrex (nb093_alpha_dummy_045 A) (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb093_alpha_dummy_044 A)
            (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_049 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb093_alpha_dummy_046 r d)
            (syn_wrex (nb093_alpha_dummy_047 r d)
              (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb093_alpha_dummy_046 r d)
            (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_050 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
            (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
              (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
              (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))).fv ∪
      ((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
            (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
              (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
              (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_051 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
            (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
              (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))).fv ∪
      ((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
            (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
              (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_052 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_001 A))
          (syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_001 A))
          (syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_053 (r : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv r) (syn_ccompl (syn_ccnv (Class.cv r))))).fv ∪
      ((syn_cnin (Class.cv r) (syn_ccompl (syn_ccnv (Class.cv r))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_054 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
      ((syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_055 (r : Var) : Var :=
  (freshVar (((Class.cv r)).fv ∪ ((syn_ccompl (syn_ccnv (Class.cv r)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_056 (A : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv ∪
      ((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_057 (r : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv r))).fv ∪ ((syn_ccnv (Class.cv r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_058 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_059 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_001 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_060 (r : Var) : Var :=
  (freshVar (((Class.cv r)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_061 (r : Var) : Var :=
  (freshVar (((Class.cv r)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_062 (A : Class) : Var :=
  (freshVar (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪
        ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A))
          (Class.cv (nb093_alpha_dummy_058 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_063 (r : Var) : Var :=
  (freshVar (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪
        ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r)
          (Class.cv (nb093_alpha_dummy_060 r)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_064 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_059 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_065 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_059 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_066 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_061 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_067 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_061 r))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_068 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_069 (r : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_070 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_064 A)
          (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
              (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv ∪
      ((Class.cab (nb093_alpha_dummy_064 A)
          (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
              (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_071 (r : Var) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_066 r)
          (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
              (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv ∪
      ((Class.cab (nb093_alpha_dummy_066 r)
          (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
              (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_072 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_065 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_073 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_065 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_074 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_067 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_075 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_067 r))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_076 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093_alpha_dummy_072 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb093_alpha_dummy_072 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb093_alpha_dummy_072 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_077 (r : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093_alpha_dummy_074 r)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb093_alpha_dummy_074 r)) (syn_c1c))).fv ∪
      ((Class.cv (nb093_alpha_dummy_074 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_078 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_079 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_080 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb093_alpha_dummy_081 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_082 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_083 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb093_alpha_dummy_084 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
          (Class.cv (nb093_alpha_dummy_080 A)))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_079 A)) (Class.cv (nb093_alpha_dummy_080 A)))).fv)
    0)

@[expose]
noncomputable def nb093_alpha_dummy_085 (r : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
          (Class.cv (nb093_alpha_dummy_083 r)))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_082 r)) (Class.cv (nb093_alpha_dummy_083 r)))).fv)
    0)

@[expose]
noncomputable def nb093_alpha_dummy_086 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_080 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_087 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_083 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_088 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb093_alpha_dummy_079 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb093_alpha_dummy_080 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_089 (r : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb093_alpha_dummy_082 r)))).fv ∪
      ((syn_ccompl (Class.cv (nb093_alpha_dummy_083 r)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_090 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_079 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_091 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_082 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_092 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_080 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_080 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_093 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_083 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_083 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_094 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_064 A)
          (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_064 A)
          (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_095 (r : Var) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_066 r)
          (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_066 r)
          (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_096 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_097 (r : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_098 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv ∪
      ((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_099 (r : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv ∪
      ((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_100 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_058 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_101 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_058 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_102 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_060 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_103 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_060 r))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_104 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_105 (r : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_106 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_100 A)
          (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
              (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv ∪
      ((Class.cab (nb093_alpha_dummy_100 A)
          (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
              (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_107 (r : Var) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_102 r)
          (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
              (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv ∪
      ((Class.cab (nb093_alpha_dummy_102 r)
          (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
              (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_108 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_101 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_109 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_101 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_110 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_103 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_111 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_103 r))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_112 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093_alpha_dummy_108 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb093_alpha_dummy_108 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb093_alpha_dummy_108 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_113 (r : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093_alpha_dummy_110 r)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb093_alpha_dummy_110 r)) (syn_c1c))).fv ∪
      ((Class.cv (nb093_alpha_dummy_110 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_114 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_115 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_116 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb093_alpha_dummy_117 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_118 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_119 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb093_alpha_dummy_120 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
          (Class.cv (nb093_alpha_dummy_116 A)))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_115 A)) (Class.cv (nb093_alpha_dummy_116 A)))).fv)
    0)

@[expose]
noncomputable def nb093_alpha_dummy_121 (r : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
          (Class.cv (nb093_alpha_dummy_119 r)))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_118 r)) (Class.cv (nb093_alpha_dummy_119 r)))).fv)
    0)

@[expose]
noncomputable def nb093_alpha_dummy_122 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_116 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_123 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_119 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_124 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb093_alpha_dummy_115 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb093_alpha_dummy_116 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_125 (r : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb093_alpha_dummy_118 r)))).fv ∪
      ((syn_ccompl (Class.cv (nb093_alpha_dummy_119 r)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_126 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_115 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_127 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_118 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_128 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_116 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_116 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_129 (r : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_119 r))).fv ∪
      ((Class.cv (nb093_alpha_dummy_119 r))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_130 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_100 A)
          (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_100 A)
          (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_131 (r : Var) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_102 r)
          (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_102 r)
          (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_132 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_133 (r : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_134 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv ∪
      ((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_135 (r : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv ∪
      ((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_136 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_045 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_137 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_045 A))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_138 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_047 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_139 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_047 r d))).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_140 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093_alpha_dummy_136 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb093_alpha_dummy_136 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb093_alpha_dummy_136 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_141 (r : Var) (d : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb093_alpha_dummy_138 r d)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb093_alpha_dummy_138 r d)) (syn_c1c))).fv ∪
      ((Class.cv (nb093_alpha_dummy_138 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_142 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_143 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_144 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb093_alpha_dummy_145 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_146 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb093_alpha_dummy_147 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb093_alpha_dummy_148 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
          (Class.cv (nb093_alpha_dummy_144 A)))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_143 A)) (Class.cv (nb093_alpha_dummy_144 A)))).fv)
    0)

@[expose]
noncomputable def nb093_alpha_dummy_149 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
          (Class.cv (nb093_alpha_dummy_147 r d)))).fv ∪
      ((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
          (Class.cv (nb093_alpha_dummy_147 r d)))).fv) 0)

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
noncomputable def nb093_alpha_dummy_150 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_144 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_151 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
      ((Class.cv (nb093_alpha_dummy_147 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_152 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb093_alpha_dummy_143 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb093_alpha_dummy_144 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_153 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb093_alpha_dummy_146 r d)))).fv ∪
      ((syn_ccompl (Class.cv (nb093_alpha_dummy_147 r d)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_154 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_143 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_155 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
      ((Class.cv (nb093_alpha_dummy_146 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_156 (A : Class) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_144 A))).fv ∪
      ((Class.cv (nb093_alpha_dummy_144 A))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_157 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093_alpha_dummy_147 r d))).fv ∪
      ((Class.cv (nb093_alpha_dummy_147 r d))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_158 (A : Class) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_044 A)
          (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_044 A)
          (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
            (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_159 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cab (nb093_alpha_dummy_046 r d)
          (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
            (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_046 r d)
          (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
            (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
              (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_160 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_161 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_162 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv ∪
      ((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv) 0)

@[expose]
noncomputable def nb093_alpha_dummy_163 (r : Var) (d : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv ∪
      ((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv) 0)

theorem nb093_fresh_000 (A : Class) :
    (nb093_alpha_dummy_038 A) ∉
      (((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_038] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb093_fresh_001 (A : Class) :
    (nb093_alpha_dummy_014 A) ∉
      (((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))))).fv)
      0

theorem nb093_fresh_002 (r : Var) (d : Var) :
    (nb093_alpha_dummy_039 r d) ∉
      (((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_039] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb093_fresh_003 (r : Var) (d : Var) :
    (nb093_alpha_dummy_015 r d) ∉
      (((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))))).fv)
      0

theorem nb093_fresh_004 (A : Class) :
    (nb093_alpha_dummy_158 A) ∉
      (((Class.cab (nb093_alpha_dummy_044 A)
            (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_044 A)
            (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_158] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_044 A)
            (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_044 A)
            (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb093_fresh_005 (A : Class) :
    (nb093_alpha_dummy_050 A) ∉
      (((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
              (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
              (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
              (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
              (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))).fv)
      0

theorem nb093_fresh_006 (r : Var) (d : Var) :
    (nb093_alpha_dummy_159 r d) ∉
      (((Class.cab (nb093_alpha_dummy_046 r d)
            (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_046 r d)
            (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_159] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_046 r d)
            (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_046 r d)
            (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb093_fresh_007 (r : Var) (d : Var) :
    (nb093_alpha_dummy_051 r d) ∉
      (((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
              (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
              (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
              (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
              (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))).fv)
      0

theorem nb093_fresh_008 (A : Class) :
    (nb093_alpha_dummy_070 A) ∉
      (((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv)
      0

theorem nb093_fresh_009 (A : Class) :
    (nb093_alpha_dummy_094 A) ∉
      (((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb093_fresh_010 (r : Var) :
    (nb093_alpha_dummy_071 r) ∉
      (((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv)
      0

theorem nb093_fresh_011 (r : Var) :
    (nb093_alpha_dummy_095 r) ∉
      (((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_095] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb093_fresh_012 (A : Class) :
    (nb093_alpha_dummy_130 A) ∉
      (((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_130] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb093_fresh_013 (A : Class) :
    (nb093_alpha_dummy_106 A) ∉
      (((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_106] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv)
      0

theorem nb093_fresh_014 (r : Var) :
    (nb093_alpha_dummy_131 r) ∉
      (((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_131] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb093_fresh_015 (r : Var) :
    (nb093_alpha_dummy_107 r) ∉
      (((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_107] using
    freshVar_not_mem
      (((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv)
      0

theorem nb093_fresh_016 (A : Class) :
    (nb093_alpha_dummy_058 A) ∉ (((Class.cv (nb093_alpha_dummy_001 A))).fv) := by
  simpa only [nb093_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_001 A))).fv) 0

theorem nb093_fresh_017 (A : Class) :
    (nb093_alpha_dummy_059 A) ∉ (((Class.cv (nb093_alpha_dummy_001 A))).fv) := by
  simpa only [nb093_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_001 A))).fv) 1

theorem nb093_distinct_018 (A : Class) :
    (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_059 A) := by
  simpa only [nb093_alpha_dummy_058, nb093_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_019 (A : Class) :
    (nb093_alpha_dummy_008 A) ∉
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_008] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv)
      0

theorem nb093_fresh_020 (A : Class) :
    (nb093_alpha_dummy_009 A) ∉
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv)
      1

theorem nb093_distinct_021 (A : Class) :
    (nb093_alpha_dummy_008 A) ≠ (nb093_alpha_dummy_009 A) := by
  simpa only [nb093_alpha_dummy_008, nb093_alpha_dummy_009] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb093_alpha_dummy_000 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_022 (A : Class) :
    (nb093_alpha_dummy_054 A) ∉
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
        ((syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_054] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
        ((syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv)
      0

theorem nb093_fresh_023 (A : Class) :
    (nb093_alpha_dummy_016 A) ∉ (((Class.cv (nb093_alpha_dummy_009 A))).fv) := by
  simpa only [nb093_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_009 A))).fv) 0

theorem nb093_fresh_024 (A : Class) :
    (nb093_alpha_dummy_017 A) ∉ (((Class.cv (nb093_alpha_dummy_009 A))).fv) := by
  simpa only [nb093_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_009 A))).fv) 1

theorem nb093_distinct_025 (A : Class) :
    (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_017 A) := by
  simpa only [nb093_alpha_dummy_016, nb093_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_009 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_026 (r : Var) (d : Var) :
    (nb093_alpha_dummy_018 r d) ∉ (((Class.cv (nb093_alpha_dummy_011 r d))).fv) := by
  simpa only [nb093_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_011 r d))).fv) 0

theorem nb093_fresh_027 (r : Var) (d : Var) :
    (nb093_alpha_dummy_019 r d) ∉ (((Class.cv (nb093_alpha_dummy_011 r d))).fv) := by
  simpa only [nb093_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_011 r d))).fv) 1

theorem nb093_distinct_028 (r : Var) (d : Var) :
    (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_019 r d) := by
  simpa only [nb093_alpha_dummy_018, nb093_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_029 (A : Class) :
    (nb093_alpha_dummy_022 A) ∉
      (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb093_fresh_030 (A : Class) :
    (nb093_alpha_dummy_023 A) ∉
      (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb093_fresh_031 (A : Class) :
    (nb093_alpha_dummy_024 A) ∉
      (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb093_distinct_032 (A : Class) :
    (nb093_alpha_dummy_022 A) ≠ (nb093_alpha_dummy_023 A) := by
  simpa only [nb093_alpha_dummy_022, nb093_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_033 (A : Class) :
    (nb093_alpha_dummy_022 A) ≠ (nb093_alpha_dummy_024 A) := by
  simpa only [nb093_alpha_dummy_022, nb093_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_034 (A : Class) :
    (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_024 A) := by
  simpa only [nb093_alpha_dummy_023, nb093_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_035 (r : Var) (d : Var) :
    (nb093_alpha_dummy_025 r d) ∉
      (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) 0

theorem nb093_fresh_036 (r : Var) (d : Var) :
    (nb093_alpha_dummy_026 r d) ∉
      (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) 1

theorem nb093_fresh_037 (r : Var) (d : Var) :
    (nb093_alpha_dummy_027 r d) ∉
      (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) 2

theorem nb093_distinct_038 (r : Var) (d : Var) :
    (nb093_alpha_dummy_025 r d) ≠ (nb093_alpha_dummy_026 r d) := by
  simpa only [nb093_alpha_dummy_025, nb093_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb093_distinct_039 (r : Var) (d : Var) :
    (nb093_alpha_dummy_025 r d) ≠ (nb093_alpha_dummy_027 r d) := by
  simpa only [nb093_alpha_dummy_025, nb093_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb093_distinct_040 (r : Var) (d : Var) :
    (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_027 r d) := by
  simpa only [nb093_alpha_dummy_026, nb093_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb093_fresh_041 (A : Class) :
    (nb093_alpha_dummy_034 A) ∉
      (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_023 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_023 A))).fv)
      0

theorem nb093_fresh_042 (A : Class) :
    (nb093_alpha_dummy_030 A) ∉
      (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_024 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_024 A))).fv)
      0

theorem nb093_fresh_043 (A : Class) :
    (nb093_alpha_dummy_036 A) ∉
      (((Class.cv (nb093_alpha_dummy_024 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_024 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_024 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_024 A))).fv)
      0

theorem nb093_fresh_044 (r : Var) (d : Var) :
    (nb093_alpha_dummy_035 r d) ∉
      (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_026 r d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_026 r d))).fv)
      0

theorem nb093_fresh_045 (r : Var) (d : Var) :
    (nb093_alpha_dummy_031 r d) ∉
      (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_027 r d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_027 r d))).fv)
      0

theorem nb093_fresh_046 (r : Var) (d : Var) :
    (nb093_alpha_dummy_037 r d) ∉
      (((Class.cv (nb093_alpha_dummy_027 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_027 r d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_027 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_027 r d))).fv)
      0

theorem nb093_fresh_047 (A : Class) :
    (nb093_alpha_dummy_136 A) ∉ (((Class.cv (nb093_alpha_dummy_045 A))).fv) := by
  simpa only [nb093_alpha_dummy_136] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_045 A))).fv) 0

theorem nb093_fresh_048 (A : Class) :
    (nb093_alpha_dummy_137 A) ∉ (((Class.cv (nb093_alpha_dummy_045 A))).fv) := by
  simpa only [nb093_alpha_dummy_137] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_045 A))).fv) 1

theorem nb093_distinct_049 (A : Class) :
    (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_137 A) := by
  simpa only [nb093_alpha_dummy_136, nb093_alpha_dummy_137] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_045 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_050 (r : Var) (d : Var) :
    (nb093_alpha_dummy_138 r d) ∉ (((Class.cv (nb093_alpha_dummy_047 r d))).fv) := by
  simpa only [nb093_alpha_dummy_138] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_047 r d))).fv) 0

theorem nb093_fresh_051 (r : Var) (d : Var) :
    (nb093_alpha_dummy_139 r d) ∉ (((Class.cv (nb093_alpha_dummy_047 r d))).fv) := by
  simpa only [nb093_alpha_dummy_139] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_047 r d))).fv) 1

theorem nb093_distinct_052 (r : Var) (d : Var) :
    (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_139 r d) := by
  simpa only [nb093_alpha_dummy_138, nb093_alpha_dummy_139] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_047 r d))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_053 (A : Class) :
    (nb093_alpha_dummy_064 A) ∉
      (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_064] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv)
      0

theorem nb093_fresh_054 (A : Class) :
    (nb093_alpha_dummy_065 A) ∉
      (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv)
      1

theorem nb093_distinct_055 (A : Class) :
    (nb093_alpha_dummy_064 A) ≠ (nb093_alpha_dummy_065 A) := by
  simpa only [nb093_alpha_dummy_064, nb093_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
        ((Class.cv (nb093_alpha_dummy_059 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_056 (A : Class) :
    (nb093_alpha_dummy_100 A) ∉
      (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_100] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv)
      0

theorem nb093_fresh_057 (A : Class) :
    (nb093_alpha_dummy_101 A) ∉
      (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_101] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv)
      1

theorem nb093_distinct_058 (A : Class) :
    (nb093_alpha_dummy_100 A) ≠ (nb093_alpha_dummy_101 A) := by
  simpa only [nb093_alpha_dummy_100, nb093_alpha_dummy_101] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪
        ((Class.cv (nb093_alpha_dummy_058 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_059 (r : Var) :
    (nb093_alpha_dummy_066 r) ∉
      (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_066] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv)
      0

theorem nb093_fresh_060 (r : Var) :
    (nb093_alpha_dummy_067 r) ∉
      (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_067] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv)
      1

theorem nb093_distinct_061 (r : Var) :
    (nb093_alpha_dummy_066 r) ≠ (nb093_alpha_dummy_067 r) := by
  simpa only [nb093_alpha_dummy_066, nb093_alpha_dummy_067] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪
        ((Class.cv (nb093_alpha_dummy_061 r))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_062 (r : Var) :
    (nb093_alpha_dummy_102 r) ∉
      (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_102] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv)
      0

theorem nb093_fresh_063 (r : Var) :
    (nb093_alpha_dummy_103 r) ∉
      (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_103] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv)
      1

theorem nb093_distinct_064 (r : Var) :
    (nb093_alpha_dummy_102 r) ≠ (nb093_alpha_dummy_103 r) := by
  simpa only [nb093_alpha_dummy_102, nb093_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪
        ((Class.cv (nb093_alpha_dummy_060 r))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_065 (A : Class) :
    (nb093_alpha_dummy_072 A) ∉ (((Class.cv (nb093_alpha_dummy_065 A))).fv) := by
  simpa only [nb093_alpha_dummy_072] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_065 A))).fv) 0

theorem nb093_fresh_066 (A : Class) :
    (nb093_alpha_dummy_073 A) ∉ (((Class.cv (nb093_alpha_dummy_065 A))).fv) := by
  simpa only [nb093_alpha_dummy_073] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_065 A))).fv) 1

theorem nb093_distinct_067 (A : Class) :
    (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_073 A) := by
  simpa only [nb093_alpha_dummy_072, nb093_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_065 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_068 (r : Var) :
    (nb093_alpha_dummy_074 r) ∉ (((Class.cv (nb093_alpha_dummy_067 r))).fv) := by
  simpa only [nb093_alpha_dummy_074] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_067 r))).fv) 0

theorem nb093_fresh_069 (r : Var) :
    (nb093_alpha_dummy_075 r) ∉ (((Class.cv (nb093_alpha_dummy_067 r))).fv) := by
  simpa only [nb093_alpha_dummy_075] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_067 r))).fv) 1

theorem nb093_distinct_070 (r : Var) :
    (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_075 r) := by
  simpa only [nb093_alpha_dummy_074, nb093_alpha_dummy_075] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_067 r))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_071 (A : Class) :
    (nb093_alpha_dummy_078 A) ∉
      (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_078] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb093_fresh_072 (A : Class) :
    (nb093_alpha_dummy_079 A) ∉
      (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_079] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb093_fresh_073 (A : Class) :
    (nb093_alpha_dummy_080 A) ∉
      (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_080] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb093_distinct_074 (A : Class) :
    (nb093_alpha_dummy_078 A) ≠ (nb093_alpha_dummy_079 A) := by
  simpa only [nb093_alpha_dummy_078, nb093_alpha_dummy_079] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_075 (A : Class) :
    (nb093_alpha_dummy_078 A) ≠ (nb093_alpha_dummy_080 A) := by
  simpa only [nb093_alpha_dummy_078, nb093_alpha_dummy_080] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_076 (A : Class) :
    (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_080 A) := by
  simpa only [nb093_alpha_dummy_079, nb093_alpha_dummy_080] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_077 (r : Var) :
    (nb093_alpha_dummy_081 r) ∉
      (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) 0

theorem nb093_fresh_078 (r : Var) :
    (nb093_alpha_dummy_082 r) ∉
      (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_082] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) 1

theorem nb093_fresh_079 (r : Var) :
    (nb093_alpha_dummy_083 r) ∉
      (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_083] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) 2

theorem nb093_distinct_080 (r : Var) :
    (nb093_alpha_dummy_081 r) ≠ (nb093_alpha_dummy_082 r) := by
  simpa only [nb093_alpha_dummy_081, nb093_alpha_dummy_082] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_081 (r : Var) :
    (nb093_alpha_dummy_081 r) ≠ (nb093_alpha_dummy_083 r) := by
  simpa only [nb093_alpha_dummy_081, nb093_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_082 (r : Var) :
    (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_083 r) := by
  simpa only [nb093_alpha_dummy_082, nb093_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_083 (A : Class) :
    (nb093_alpha_dummy_090 A) ∉
      (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_079 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_090] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_079 A))).fv)
      0

theorem nb093_fresh_084 (A : Class) :
    (nb093_alpha_dummy_086 A) ∉
      (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_086] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv)
      0

theorem nb093_fresh_085 (A : Class) :
    (nb093_alpha_dummy_092 A) ∉
      (((Class.cv (nb093_alpha_dummy_080 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_092] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_080 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv)
      0

theorem nb093_fresh_086 (r : Var) :
    (nb093_alpha_dummy_091 r) ∉
      (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_082 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_091] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_082 r))).fv)
      0

theorem nb093_fresh_087 (r : Var) :
    (nb093_alpha_dummy_087 r) ∉
      (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_087] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv)
      0

theorem nb093_fresh_088 (r : Var) :
    (nb093_alpha_dummy_093 r) ∉
      (((Class.cv (nb093_alpha_dummy_083 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_083 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv)
      0

theorem nb093_fresh_089 (A : Class) :
    (nb093_alpha_dummy_108 A) ∉ (((Class.cv (nb093_alpha_dummy_101 A))).fv) := by
  simpa only [nb093_alpha_dummy_108] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_101 A))).fv) 0

theorem nb093_fresh_090 (A : Class) :
    (nb093_alpha_dummy_109 A) ∉ (((Class.cv (nb093_alpha_dummy_101 A))).fv) := by
  simpa only [nb093_alpha_dummy_109] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_101 A))).fv) 1

theorem nb093_distinct_091 (A : Class) :
    (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_109 A) := by
  simpa only [nb093_alpha_dummy_108, nb093_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_101 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_092 (r : Var) :
    (nb093_alpha_dummy_110 r) ∉ (((Class.cv (nb093_alpha_dummy_103 r))).fv) := by
  simpa only [nb093_alpha_dummy_110] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_103 r))).fv) 0

theorem nb093_fresh_093 (r : Var) :
    (nb093_alpha_dummy_111 r) ∉ (((Class.cv (nb093_alpha_dummy_103 r))).fv) := by
  simpa only [nb093_alpha_dummy_111] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_103 r))).fv) 1

theorem nb093_distinct_094 (r : Var) :
    (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_111 r) := by
  simpa only [nb093_alpha_dummy_110, nb093_alpha_dummy_111] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_103 r))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb093_fresh_095 (A : Class) :
    (nb093_alpha_dummy_114 A) ∉
      (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_114] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb093_fresh_096 (A : Class) :
    (nb093_alpha_dummy_115 A) ∉
      (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_115] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb093_fresh_097 (A : Class) :
    (nb093_alpha_dummy_116 A) ∉
      (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_116] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb093_distinct_098 (A : Class) :
    (nb093_alpha_dummy_114 A) ≠ (nb093_alpha_dummy_115 A) := by
  simpa only [nb093_alpha_dummy_114, nb093_alpha_dummy_115] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_099 (A : Class) :
    (nb093_alpha_dummy_114 A) ≠ (nb093_alpha_dummy_116 A) := by
  simpa only [nb093_alpha_dummy_114, nb093_alpha_dummy_116] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_100 (A : Class) :
    (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_116 A) := by
  simpa only [nb093_alpha_dummy_115, nb093_alpha_dummy_116] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_101 (r : Var) :
    (nb093_alpha_dummy_117 r) ∉
      (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_117] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) 0

theorem nb093_fresh_102 (r : Var) :
    (nb093_alpha_dummy_118 r) ∉
      (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_118] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) 1

theorem nb093_fresh_103 (r : Var) :
    (nb093_alpha_dummy_119 r) ∉
      (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_119] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) 2

theorem nb093_distinct_104 (r : Var) :
    (nb093_alpha_dummy_117 r) ≠ (nb093_alpha_dummy_118 r) := by
  simpa only [nb093_alpha_dummy_117, nb093_alpha_dummy_118] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_105 (r : Var) :
    (nb093_alpha_dummy_117 r) ≠ (nb093_alpha_dummy_119 r) := by
  simpa only [nb093_alpha_dummy_117, nb093_alpha_dummy_119] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_106 (r : Var) :
    (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_119 r) := by
  simpa only [nb093_alpha_dummy_118, nb093_alpha_dummy_119] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_107 (A : Class) :
    (nb093_alpha_dummy_126 A) ∉
      (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_115 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_126] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_115 A))).fv)
      0

theorem nb093_fresh_108 (A : Class) :
    (nb093_alpha_dummy_122 A) ∉
      (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv)
      0

theorem nb093_fresh_109 (A : Class) :
    (nb093_alpha_dummy_128 A) ∉
      (((Class.cv (nb093_alpha_dummy_116 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_128] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_116 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv)
      0

theorem nb093_fresh_110 (r : Var) :
    (nb093_alpha_dummy_127 r) ∉
      (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_118 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_127] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_118 r))).fv)
      0

theorem nb093_fresh_111 (r : Var) :
    (nb093_alpha_dummy_123 r) ∉
      (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_123] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv)
      0

theorem nb093_fresh_112 (r : Var) :
    (nb093_alpha_dummy_129 r) ∉
      (((Class.cv (nb093_alpha_dummy_119 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_129] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_119 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv)
      0

theorem nb093_fresh_113 (A : Class) :
    (nb093_alpha_dummy_142 A) ∉
      (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_142] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb093_fresh_114 (A : Class) :
    (nb093_alpha_dummy_143 A) ∉
      (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_143] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb093_fresh_115 (A : Class) :
    (nb093_alpha_dummy_144 A) ∉
      (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_144] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb093_distinct_116 (A : Class) :
    (nb093_alpha_dummy_142 A) ≠ (nb093_alpha_dummy_143 A) := by
  simpa only [nb093_alpha_dummy_142, nb093_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb093_distinct_117 (A : Class) :
    (nb093_alpha_dummy_142 A) ≠ (nb093_alpha_dummy_144 A) := by
  simpa only [nb093_alpha_dummy_142, nb093_alpha_dummy_144] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb093_distinct_118 (A : Class) :
    (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_144 A) := by
  simpa only [nb093_alpha_dummy_143, nb093_alpha_dummy_144] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb093_fresh_119 (r : Var) (d : Var) :
    (nb093_alpha_dummy_145 r d) ∉
      (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_145] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) 0

theorem nb093_fresh_120 (r : Var) (d : Var) :
    (nb093_alpha_dummy_146 r d) ∉
      (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_146] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) 1

theorem nb093_fresh_121 (r : Var) (d : Var) :
    (nb093_alpha_dummy_147 r d) ∉
      (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb093_alpha_dummy_147] using
    freshVar_not_mem (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) 2

theorem nb093_distinct_122 (r : Var) (d : Var) :
    (nb093_alpha_dummy_145 r d) ≠ (nb093_alpha_dummy_146 r d) := by
  simpa only [nb093_alpha_dummy_145, nb093_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb093_distinct_123 (r : Var) (d : Var) :
    (nb093_alpha_dummy_145 r d) ≠ (nb093_alpha_dummy_147 r d) := by
  simpa only [nb093_alpha_dummy_145, nb093_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb093_distinct_124 (r : Var) (d : Var) :
    (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_147 r d) := by
  simpa only [nb093_alpha_dummy_146, nb093_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb093_fresh_125 (A : Class) :
    (nb093_alpha_dummy_154 A) ∉
      (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_143 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_143 A))).fv)
      0

theorem nb093_fresh_126 (A : Class) :
    (nb093_alpha_dummy_150 A) ∉
      (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_150] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv)
      0

theorem nb093_fresh_127 (A : Class) :
    (nb093_alpha_dummy_156 A) ∉
      (((Class.cv (nb093_alpha_dummy_144 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_156] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_144 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv)
      0

theorem nb093_fresh_128 (r : Var) (d : Var) :
    (nb093_alpha_dummy_155 r d) ∉
      (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_146 r d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_155] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_146 r d))).fv)
      0

theorem nb093_fresh_129 (r : Var) (d : Var) :
    (nb093_alpha_dummy_151 r d) ∉
      (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_147 r d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_151] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_147 r d))).fv)
      0

theorem nb093_fresh_130 (r : Var) (d : Var) :
    (nb093_alpha_dummy_157 r d) ∉
      (((Class.cv (nb093_alpha_dummy_147 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_147 r d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_157] using
    freshVar_not_mem
      (((Class.cv (nb093_alpha_dummy_147 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_147 r d))).fv)
      0

theorem nb093_fresh_131 (r : Var) : (nb093_alpha_dummy_060 r) ∉ (((Class.cv r)).fv) := by
  simpa only [nb093_alpha_dummy_060] using freshVar_not_mem (((Class.cv r)).fv) 0

theorem nb093_fresh_132 (r : Var) : (nb093_alpha_dummy_061 r) ∉ (((Class.cv r)).fv) := by
  simpa only [nb093_alpha_dummy_061] using freshVar_not_mem (((Class.cv r)).fv) 1

theorem nb093_distinct_133 (r : Var) :
    (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_061 r) := by
  simpa only [nb093_alpha_dummy_060, nb093_alpha_dummy_061] using
    (freshVar_injective (((Class.cv r)).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_134 (r : Var) (d : Var) :
    (nb093_alpha_dummy_010 r d) ∉ (((Class.cv r)).fv ∪ ((Class.cv d)).fv) := by
  simpa only [nb093_alpha_dummy_010] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv d)).fv) 0

theorem nb093_fresh_135 (r : Var) (d : Var) :
    (nb093_alpha_dummy_011 r d) ∉ (((Class.cv r)).fv ∪ ((Class.cv d)).fv) := by
  simpa only [nb093_alpha_dummy_011] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv d)).fv) 1

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

theorem nb093_distinct_136 (r : Var) (d : Var) :
    (nb093_alpha_dummy_010 r d) ≠ (nb093_alpha_dummy_011 r d) := by
  simpa only [nb093_alpha_dummy_010, nb093_alpha_dummy_011] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_137 (r : Var) :
    (nb093_alpha_dummy_055 r) ∉
      (((Class.cv r)).fv ∪ ((syn_ccompl (syn_ccnv (Class.cv r)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_055] using
    freshVar_not_mem (((Class.cv r)).fv ∪ ((syn_ccompl (syn_ccnv (Class.cv r)))).fv) 0

theorem nb093_fresh_138 (A : Class) :
    (nb093_alpha_dummy_020 A) ∉
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_016 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_016 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_016 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_016 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_016 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_016 A))).fv)
      0

theorem nb093_fresh_139 (r : Var) (d : Var) :
    (nb093_alpha_dummy_021 r d) ∉
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_018 r d)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_018 r d)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_018 r d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_018 r d)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_018 r d)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_018 r d))).fv)
      0

theorem nb093_fresh_140 (A : Class) :
    (nb093_alpha_dummy_076 A) ∉
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_072 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_072 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_072 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_076] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_072 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_072 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_072 A))).fv)
      0

theorem nb093_fresh_141 (r : Var) :
    (nb093_alpha_dummy_077 r) ∉
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_074 r)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_074 r)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_074 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_077] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_074 r)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_074 r)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_074 r))).fv)
      0

theorem nb093_fresh_142 (A : Class) :
    (nb093_alpha_dummy_112 A) ∉
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_108 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_108 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_108 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_112] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_108 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_108 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_108 A))).fv)
      0

theorem nb093_fresh_143 (r : Var) :
    (nb093_alpha_dummy_113 r) ∉
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_110 r)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_110 r)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_110 r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_113] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_110 r)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_110 r)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_110 r))).fv)
      0

theorem nb093_fresh_144 (A : Class) :
    (nb093_alpha_dummy_140 A) ∉
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_136 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_136 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_136 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_140] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_136 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_136 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_136 A))).fv)
      0

theorem nb093_fresh_145 (r : Var) (d : Var) :
    (nb093_alpha_dummy_141 r d) ∉
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_138 r d)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_138 r d)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_138 r d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_141] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_138 r d)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_138 r d)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_138 r d))).fv)
      0

theorem nb093_fresh_146 (A : Class) :
    (nb093_alpha_dummy_056 A) ∉
      (((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv ∪
        ((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_056] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv ∪
        ((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv)
      0

theorem nb093_fresh_147 (r : Var) :
    (nb093_alpha_dummy_057 r) ∉
      (((syn_ccnv (Class.cv r))).fv ∪ ((syn_ccnv (Class.cv r))).fv) :=
  by
  simpa only [nb093_alpha_dummy_057] using
    freshVar_not_mem (((syn_ccnv (Class.cv r))).fv ∪ ((syn_ccnv (Class.cv r))).fv) 0

theorem nb093_fresh_148 (A : Class) :
    (nb093_alpha_dummy_012 A) ∉
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb093_fresh_149 (r : Var) (d : Var) :
    (nb093_alpha_dummy_013 r d) ∉
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_013] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb093_fresh_150 (A : Class) :
    (nb093_alpha_dummy_048 A) ∉
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
                (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_044 A)
              (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
                (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_044 A)
              (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb093_fresh_151 (r : Var) (d : Var) :
    (nb093_alpha_dummy_049 r d) ∉
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
                (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_046 r d)
              (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
                (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_046 r d)
              (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb093_fresh_152 (A : Class) :
    (nb093_alpha_dummy_068 A) ∉
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_068] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb093_fresh_153 (r : Var) :
    (nb093_alpha_dummy_069 r) ∉
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_069] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb093_fresh_154 (A : Class) :
    (nb093_alpha_dummy_104 A) ∉
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_104] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb093_fresh_155 (r : Var) :
    (nb093_alpha_dummy_105 r) ∉
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_105] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb093_fresh_156 (A : Class) :
    (nb093_alpha_dummy_032 A) ∉
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_023 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_024 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_032] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_023 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_024 A)))).fv)
      0

theorem nb093_fresh_157 (r : Var) (d : Var) :
    (nb093_alpha_dummy_033 r d) ∉
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_026 r d)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_027 r d)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_033] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_026 r d)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_027 r d)))).fv)
      0

theorem nb093_fresh_158 (A : Class) :
    (nb093_alpha_dummy_088 A) ∉
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_079 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_080 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_088] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_079 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_080 A)))).fv)
      0

theorem nb093_fresh_159 (r : Var) :
    (nb093_alpha_dummy_089 r) ∉
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_082 r)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_083 r)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_089] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_082 r)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_083 r)))).fv)
      0

theorem nb093_fresh_160 (A : Class) :
    (nb093_alpha_dummy_124 A) ∉
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_115 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_116 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_124] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_115 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_116 A)))).fv)
      0

theorem nb093_fresh_161 (r : Var) :
    (nb093_alpha_dummy_125 r) ∉
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_118 r)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_119 r)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_125] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_118 r)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_119 r)))).fv)
      0

theorem nb093_fresh_162 (A : Class) :
    (nb093_alpha_dummy_152 A) ∉
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_143 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_144 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_143 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_144 A)))).fv)
      0

theorem nb093_fresh_163 (r : Var) (d : Var) :
    (nb093_alpha_dummy_153 r d) ∉
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_146 r d)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_147 r d)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_153] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_146 r d)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_147 r d)))).fv)
      0

theorem nb093_fresh_164 (A : Class) :
    (nb093_alpha_dummy_040 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb093_fresh_165 (r : Var) (d : Var) :
    (nb093_alpha_dummy_041 r d) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb093_fresh_166 (A : Class) :
    (nb093_alpha_dummy_160 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_160] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb093_fresh_167 (r : Var) (d : Var) :
    (nb093_alpha_dummy_161 r d) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_161] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb093_fresh_168 (A : Class) :
    (nb093_alpha_dummy_096 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_096] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb093_fresh_169 (r : Var) :
    (nb093_alpha_dummy_097 r) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_097] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb093_fresh_170 (A : Class) :
    (nb093_alpha_dummy_132 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_132] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb093_fresh_171 (r : Var) :
    (nb093_alpha_dummy_133 r) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_133] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb093_fresh_172 (A : Class) :
    (nb093_alpha_dummy_044 A) ∉
      (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
        ((Class.cv (nb093_alpha_dummy_000 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
        ((Class.cv (nb093_alpha_dummy_000 A))).fv)
      0

theorem nb093_fresh_173 (A : Class) :
    (nb093_alpha_dummy_045 A) ∉
      (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
        ((Class.cv (nb093_alpha_dummy_000 A))).fv) :=
  by
  simpa only [nb093_alpha_dummy_045] using
    freshVar_not_mem
      (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
        ((Class.cv (nb093_alpha_dummy_000 A))).fv)
      1

theorem nb093_distinct_174 (A : Class) :
    (nb093_alpha_dummy_044 A) ≠ (nb093_alpha_dummy_045 A) := by
  simpa only [nb093_alpha_dummy_044, nb093_alpha_dummy_045] using
    (freshVar_injective (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
        ((Class.cv (nb093_alpha_dummy_000 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_175 (r : Var) (d : Var) :
    (nb093_alpha_dummy_046 r d) ∉
      (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) :=
  by
  simpa only [nb093_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) 0

theorem nb093_fresh_176 (r : Var) (d : Var) :
    (nb093_alpha_dummy_047 r d) ∉
      (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) :=
  by
  simpa only [nb093_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) 1

theorem nb093_distinct_177 (r : Var) (d : Var) :
    (nb093_alpha_dummy_046 r d) ≠ (nb093_alpha_dummy_047 r d) := by
  simpa only [nb093_alpha_dummy_046, nb093_alpha_dummy_047] using
    (freshVar_injective
      (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb093_fresh_178 (A : Class) :
    (nb093_alpha_dummy_004 A) ∉
      (((syn_clntpc A)).fv ∪ ((syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A)
            (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_004] using
    freshVar_not_mem
      (((syn_clntpc A)).fv ∪ ((syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A)
            (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A))))).fv)
      0

theorem nb093_fresh_179 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_005 A r d) ∉
      (((syn_clntpc A)).fv ∪ ((syn_copab r d
            (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
              (Class.cv d)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_005] using
    freshVar_not_mem
      (((syn_clntpc A)).fv ∪ ((syn_copab r d
            (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
              (Class.cv d)))).fv)
      0

theorem nb093_fresh_180 (A : Class) :
    (nb093_alpha_dummy_052 A) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))))).fv)
      0

theorem nb093_fresh_181 (A : Class) :
    (nb093_alpha_dummy_028 A) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
            (Class.cv (nb093_alpha_dummy_024 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
            (Class.cv (nb093_alpha_dummy_024 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
            (Class.cv (nb093_alpha_dummy_024 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
            (Class.cv (nb093_alpha_dummy_024 A)))).fv)
      0

theorem nb093_fresh_182 (r : Var) (d : Var) :
    (nb093_alpha_dummy_029 r d) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
            (Class.cv (nb093_alpha_dummy_027 r d)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
            (Class.cv (nb093_alpha_dummy_027 r d)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
            (Class.cv (nb093_alpha_dummy_027 r d)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
            (Class.cv (nb093_alpha_dummy_027 r d)))).fv)
      0

theorem nb093_fresh_183 (A : Class) :
    (nb093_alpha_dummy_084 A) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
            (Class.cv (nb093_alpha_dummy_080 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
            (Class.cv (nb093_alpha_dummy_080 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_084] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
            (Class.cv (nb093_alpha_dummy_080 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
            (Class.cv (nb093_alpha_dummy_080 A)))).fv)
      0

theorem nb093_fresh_184 (r : Var) :
    (nb093_alpha_dummy_085 r) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
            (Class.cv (nb093_alpha_dummy_083 r)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
            (Class.cv (nb093_alpha_dummy_083 r)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_085] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
            (Class.cv (nb093_alpha_dummy_083 r)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
            (Class.cv (nb093_alpha_dummy_083 r)))).fv)
      0

theorem nb093_fresh_185 (A : Class) :
    (nb093_alpha_dummy_120 A) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
            (Class.cv (nb093_alpha_dummy_116 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
            (Class.cv (nb093_alpha_dummy_116 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_120] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
            (Class.cv (nb093_alpha_dummy_116 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
            (Class.cv (nb093_alpha_dummy_116 A)))).fv)
      0

theorem nb093_fresh_186 (r : Var) :
    (nb093_alpha_dummy_121 r) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
            (Class.cv (nb093_alpha_dummy_119 r)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
            (Class.cv (nb093_alpha_dummy_119 r)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_121] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
            (Class.cv (nb093_alpha_dummy_119 r)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
            (Class.cv (nb093_alpha_dummy_119 r)))).fv)
      0

theorem nb093_fresh_187 (A : Class) :
    (nb093_alpha_dummy_148 A) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
            (Class.cv (nb093_alpha_dummy_144 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
            (Class.cv (nb093_alpha_dummy_144 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_148] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
            (Class.cv (nb093_alpha_dummy_144 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
            (Class.cv (nb093_alpha_dummy_144 A)))).fv)
      0

theorem nb093_fresh_188 (r : Var) (d : Var) :
    (nb093_alpha_dummy_149 r d) ∉
      (((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
            (Class.cv (nb093_alpha_dummy_147 r d)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
            (Class.cv (nb093_alpha_dummy_147 r d)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_149] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
            (Class.cv (nb093_alpha_dummy_147 r d)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
            (Class.cv (nb093_alpha_dummy_147 r d)))).fv)
      0

theorem nb093_fresh_189 (r : Var) :
    (nb093_alpha_dummy_053 r) ∉
      (((syn_cnin (Class.cv r) (syn_ccompl (syn_ccnv (Class.cv r))))).fv ∪
        ((syn_cnin (Class.cv r) (syn_ccompl (syn_ccnv (Class.cv r))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_053] using
    freshVar_not_mem
      (((syn_cnin (Class.cv r) (syn_ccompl (syn_ccnv (Class.cv r))))).fv ∪
        ((syn_cnin (Class.cv r) (syn_ccompl (syn_ccnv (Class.cv r))))).fv)
      0

theorem nb093_fresh_190 (A : Class) :
    (nb093_alpha_dummy_002 A) ∉
      (((syn_cnin (syn_clntpc A) (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A)
              (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv ∪
        ((syn_cnin (syn_clntpc A) (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A)
              (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_002] using
    freshVar_not_mem
      (((syn_cnin (syn_clntpc A) (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A)
              (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv ∪
        ((syn_cnin (syn_clntpc A) (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A)
              (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv)
      0

theorem nb093_fresh_191 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_003 A r d) ∉
      (((syn_cnin (syn_clntpc A) (syn_copab r d
              (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
                (Class.cv d))))).fv ∪ ((syn_cnin (syn_clntpc A) (syn_copab r d
              (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
                (Class.cv d))))).fv) :=
  by
  simpa only [nb093_alpha_dummy_003] using
    freshVar_not_mem
      (((syn_cnin (syn_clntpc A) (syn_copab r d
              (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
                (Class.cv d))))).fv ∪ ((syn_cnin (syn_clntpc A) (syn_copab r d
              (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
                (Class.cv d))))).fv)
      0

theorem nb093_fresh_192 (A : Class) :
    (nb093_alpha_dummy_042 A) ∉
      (((syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))).fv)
      0

theorem nb093_fresh_193 (r : Var) (d : Var) :
    (nb093_alpha_dummy_043 r d) ∉
      (((syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))).fv)
      0

theorem nb093_fresh_194 (A : Class) :
    (nb093_alpha_dummy_162 A) ∉
      (((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_162] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv)
      0

theorem nb093_fresh_195 (r : Var) (d : Var) :
    (nb093_alpha_dummy_163 r d) ∉
      (((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_163] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv)
      0

theorem nb093_fresh_196 (A : Class) :
    (nb093_alpha_dummy_098 A) ∉
      (((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_098] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv)
      0

theorem nb093_fresh_197 (r : Var) :
    (nb093_alpha_dummy_099 r) ∉
      (((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_099] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv)
      0

theorem nb093_fresh_198 (A : Class) :
    (nb093_alpha_dummy_134 A) ∉
      (((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_134] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv)
      0

theorem nb093_fresh_199 (r : Var) :
    (nb093_alpha_dummy_135 r) ∉
      (((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_135] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv)
      0

theorem nb093_fresh_200 (A : Class) : (nb093_alpha_dummy_000 A) ∉ ((A).fv) := by
  simpa only [nb093_alpha_dummy_000] using freshVar_not_mem ((A).fv) 0

theorem nb093_fresh_201 (A : Class) : (nb093_alpha_dummy_001 A) ∉ ((A).fv) := by
  simpa only [nb093_alpha_dummy_001] using freshVar_not_mem ((A).fv) 1

theorem nb093_distinct_202 (A : Class) :
    (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_001 A) := by
  simpa only [nb093_alpha_dummy_000, nb093_alpha_dummy_001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb093_fresh_203 (A : Class) :
    (nb093_alpha_dummy_006 A) ∉
      (({(nb093_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_000 A)} : Finset Var) ∪
        ((syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
              (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
            (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_006] using
    freshVar_not_mem
      (({(nb093_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_000 A)} : Finset Var) ∪
        ((syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
              (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
            (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))).fv)
      0

theorem nb093_fresh_204 (A : Class) :
    (nb093_alpha_dummy_062 A) ∉
      (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A))
            (Class.cv (nb093_alpha_dummy_058 A)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_062] using
    freshVar_not_mem
      (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A))
            (Class.cv (nb093_alpha_dummy_058 A)))).fv)
      0

theorem nb093_fresh_205 (r : Var) :
    (nb093_alpha_dummy_063 r) ∉
      (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪ ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r)
            (Class.cv (nb093_alpha_dummy_060 r)))).fv) :=
  by
  simpa only [nb093_alpha_dummy_063] using
    freshVar_not_mem
      (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪ ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r)
            (Class.cv (nb093_alpha_dummy_060 r)))).fv)
      0

theorem nb093_fresh_206 (r : Var) (d : Var) :
    (nb093_alpha_dummy_007 r d) ∉
      (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
        ((syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
            (Class.cv d))).fv) :=
  by
  simpa only [nb093_alpha_dummy_007] using
    freshVar_not_mem
      (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
        ((syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
            (Class.cv d))).fv)
      0

theorem nb093_support_mem_0000 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (({(nb093_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_000 A)} : Finset Var) ∪
        ((syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
              (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
            (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0001 (r : Var) (d : Var) :
    r ∈
      (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
        ((syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
            (Class.cv d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0002 (A : Class) :
    (nb093_alpha_dummy_000 A) ∈
      (({(nb093_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_000 A)} : Finset Var) ∪
        ((syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
              (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
            (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0003 (r : Var) (d : Var) :
    d ∈
      (({ r } : Finset Var) ∪ ({ d } : Finset Var) ∪
        ((syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
            (Class.cv d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0004 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0005 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_008 A) from (by
          unfold nb093_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_009 A) from (by
            unfold nb093_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0006 (r : Var) (d : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((Class.cv d)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0007 (r : Var) (d : Var) :
    r ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show r ≠ (nb093_alpha_dummy_010 r d) from (by
          unfold nb093_alpha_dummy_010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show r ≠ (nb093_alpha_dummy_011 r d) from (by
            unfold nb093_alpha_dummy_011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0008 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_008 A) from (by
          unfold nb093_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_009 A) from (by
            unfold nb093_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0009 (r : Var) (d : Var) :
    r ∈
      (((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show r ≠ (nb093_alpha_dummy_010 r d) from (by
          unfold nb093_alpha_dummy_010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show r ≠ (nb093_alpha_dummy_011 r d) from (by
            unfold nb093_alpha_dummy_011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0010 (A : Class) :
    (nb093_alpha_dummy_009 A) ∈ (((Class.cv (nb093_alpha_dummy_009 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0011 (r : Var) (d : Var) :
    (nb093_alpha_dummy_011 r d) ∈ (((Class.cv (nb093_alpha_dummy_011 r d))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0012 (A : Class) :
    (nb093_alpha_dummy_016 A) ∈
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_016 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_016 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_016 A))).fv) :=
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

theorem nb093_support_mem_0013 (r : Var) (d : Var) :
    (nb093_alpha_dummy_018 r d) ∈
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_018 r d)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_018 r d)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_018 r d))).fv) :=
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

theorem nb093_support_mem_0014 (A : Class) :
    (nb093_alpha_dummy_016 A) ∈
      (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0015 (r : Var) (d : Var) :
    (nb093_alpha_dummy_018 r d) ∈
      (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0016 (A : Class) :
    (nb093_alpha_dummy_023 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
            (Class.cv (nb093_alpha_dummy_024 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
            (Class.cv (nb093_alpha_dummy_024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0017 (r : Var) (d : Var) :
    (nb093_alpha_dummy_026 r d) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
            (Class.cv (nb093_alpha_dummy_027 r d)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
            (Class.cv (nb093_alpha_dummy_027 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0018 (A : Class) :
    (nb093_alpha_dummy_023 A) ∈
      (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_024 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0019 (r : Var) (d : Var) :
    (nb093_alpha_dummy_026 r d) ∈
      (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_027 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0020 (A : Class) :
    (nb093_alpha_dummy_024 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
            (Class.cv (nb093_alpha_dummy_024 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_023 A))
            (Class.cv (nb093_alpha_dummy_024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0021 (r : Var) (d : Var) :
    (nb093_alpha_dummy_027 r d) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
            (Class.cv (nb093_alpha_dummy_027 r d)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_026 r d))
            (Class.cv (nb093_alpha_dummy_027 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0022 (A : Class) :
    (nb093_alpha_dummy_024 A) ∈
      (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_024 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0023 (r : Var) (d : Var) :
    (nb093_alpha_dummy_027 r d) ∈
      (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_027 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0024 (A : Class) :
    (nb093_alpha_dummy_023 A) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_023 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0025 (r : Var) (d : Var) :
    (nb093_alpha_dummy_026 r d) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_026 r d)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_027 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0026 (A : Class) :
    (nb093_alpha_dummy_023 A) ∈
      (((Class.cv (nb093_alpha_dummy_023 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_023 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0027 (r : Var) (d : Var) :
    (nb093_alpha_dummy_026 r d) ∈
      (((Class.cv (nb093_alpha_dummy_026 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_026 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0028 (A : Class) :
    (nb093_alpha_dummy_024 A) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_023 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_024 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0029 (r : Var) (d : Var) :
    (nb093_alpha_dummy_027 r d) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_026 r d)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_027 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0030 (A : Class) :
    (nb093_alpha_dummy_024 A) ∈
      (((Class.cv (nb093_alpha_dummy_024 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_024 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0031 (r : Var) (d : Var) :
    (nb093_alpha_dummy_027 r d) ∈
      (((Class.cv (nb093_alpha_dummy_027 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_027 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0032 (A : Class) :
    (nb093_alpha_dummy_000 A) ∈
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0033 (A : Class) :
    (nb093_alpha_dummy_000 A) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_008 A) from (by
          unfold nb093_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_009 A) from (by
            unfold nb093_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0034 (r : Var) (d : Var) :
    d ∈ (((Class.cv r)).fv ∪ ((Class.cv d)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0035 (r : Var) (d : Var) :
    d ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb093_alpha_dummy_010 r d) from (by
          unfold nb093_alpha_dummy_010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb093_alpha_dummy_011 r d) from (by
            unfold nb093_alpha_dummy_011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0036 (A : Class) :
    (nb093_alpha_dummy_000 A) ∈
      (((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_008 A)
            (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_008 A) from (by
          unfold nb093_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_009 A) from (by
            unfold nb093_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0037 (r : Var) (d : Var) :
    d ∈
      (((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_010 r d)
            (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb093_alpha_dummy_010 r d) from (by
          unfold nb093_alpha_dummy_010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb093_alpha_dummy_011 r d) from (by
            unfold nb093_alpha_dummy_011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0038 (A : Class) :
    (nb093_alpha_dummy_009 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0039 (r : Var) (d : Var) :
    (nb093_alpha_dummy_011 r d) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0040 (A : Class) :
    (nb093_alpha_dummy_009 A) ∈
      (((syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0041 (r : Var) (d : Var) :
    (nb093_alpha_dummy_011 r d) ∈
      (((syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0042 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
        ((Class.cv (nb093_alpha_dummy_000 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cdif]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0043 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
                (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_044 A)
              (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_044 A) from (by
          unfold nb093_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0042 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_045 A) from (by
            unfold nb093_alpha_dummy_045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0042 A) 1))))
    · rw [fv_syn_cdif]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0044 (r : Var) (d : Var) :
    r ∈ (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cdif]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0045 (r : Var) (d : Var) :
    r ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
                (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_046 r d)
              (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show r ≠ (nb093_alpha_dummy_046 r d) from (by
          unfold nb093_alpha_dummy_046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0044 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show r ≠ (nb093_alpha_dummy_047 r d) from (by
            unfold nb093_alpha_dummy_047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0044 r d) 1))))
    · rw [fv_syn_cdif]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0046 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
              (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
              (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_044 A) from (by
          unfold nb093_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0042 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_045 A) from (by
            unfold nb093_alpha_dummy_045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0042 A) 1))))
    · rw [fv_syn_cdif]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0047 (r : Var) (d : Var) :
    r ∈
      (((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
              (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
              (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show r ≠ (nb093_alpha_dummy_046 r d) from (by
          unfold nb093_alpha_dummy_046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0044 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show r ≠ (nb093_alpha_dummy_047 r d) from (by
            unfold nb093_alpha_dummy_047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0044 r d) 1))))
    · rw [fv_syn_cdif]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0048 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0049 (r : Var) :
    r ∈
      (((syn_cnin (Class.cv r) (syn_ccompl (syn_ccnv (Class.cv r))))).fv ∪
        ((syn_cnin (Class.cv r) (syn_ccompl (syn_ccnv (Class.cv r))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0050 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
        ((syn_ccompl (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
